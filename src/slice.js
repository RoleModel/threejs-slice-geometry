//var facesFromEdges = require('./faces-from-edges.js');

var earcut = require('earcut')

module.exports = function(THREE) {
    "use strict";

    var FRONT = 'front';
    var BACK = 'back';
    var ON = 'on';

    var FACE_KEYS = ['a', 'b', 'c'];

    THREE.Vector3.prototype.equals = function(v, tolerance) {
      if (tolerance === undefined) {
        return ((v.x === this.x) && (v.y === this.y) && (v.z === this.z));
      } else {
        return ((Math.abs(v.x - this.x) < tolerance) && (Math.abs(v.y - this.y) < tolerance) && (Math.abs(v.z - this.z) < tolerance));
      }
    }

    const getTransform = (plane) => {
      const a = new THREE.Vector3(0, 0, 1)
      const q = new THREE.Quaternion()
      const b = plane.normal
      q.setFromUnitVectors(b, a)
      return q
    }

    const clamp = (v, min, max) => {
      if(v < min) {
        return min
      } else if(v > max) {
        return max
      } else {
        return v
      }
    }

    // based on a SDF shader implemented by Inigo Quilez under MIT license
    // https://www.shadertoy.com/view/wdBXRW
    const distanceToContour = function(vertices, p) {
      const point = new THREE.Vector2(p.x, p.y)

      const num = vertices.length
      const a1 = point.clone().sub(vertices[0]) // Vector from first vertex to point
      let d = a1.clone().dot(a1) // squared length
      let s = 1.0 // sign
      for( let i=0, j=num-1; i<num; j=i, i++ ) {
          // distance
          const e = vertices[j].clone().sub(vertices[i]) // Vector from current vertex to previous vertex
          const w = point.clone().sub(vertices[i]) // Vector from current vertex to point

          const b = w.clone().sub(
            e.clone().multiplyScalar(
              clamp((w.clone().dot(e)/e.clone().dot(e)), 0.0, 1.0) // or `clamp`
            )
          ) // Vector from closest point on edge i-j to point
          d = Math.min( d, b.clone().dot(b) ) // minimum square distance

          // winding number from http://geomalgorithms.com/a03-_inclusion.html
          const cond = [
            point.y >= vertices[i].y,
            point.y < vertices[j].y,
            (e.x * w.y) > (e.y * w.x)
          ]
          if( cond.every(con => con) || cond.every(con => !con) ) s*=-1.0
      }

      const v = s*Math.sqrt(d)
      return v
    }

    // map contours
    //   determine if overlapping/enclosed? (any points within SDF defined by contour)
    //   if overlapping/contained, then attach to parent contour and mark as hole
    const associateHoles = function(contours) {
      const holeIndexes = []
      for(let i = 0; i < contours.length; i++) {
        const contour = contours[i]

        if(holeIndexes.includes(i)) { continue; } // already determined to be a child

        contour.contour2d = contour.map(v => {
          const p = v.clone().applyQuaternion(contour.transform)
          return new THREE.Vector2(p.x, p.y)
        })
        contour.contour2d.pop() // clean up duplicated end vertice

        for(let j = 0; j < contours.length; j++) {
          if(i === j || holeIndexes.includes(j)) { continue; }

          const subject = contours[j]

          // applying a less than robust, but highly efficient approach...
          // assuming clean geometry, two boundary contours will not be intersecting,
          //   they will either be entirely within or entirely without an alternative contour
          // therefore, we can check a single point, and if it falls within the putative root,
          //   we can consider all its contour to be so.
          // And if it fails to fall within... we can move on to the next contour.
          // If it is on the line, we can reevaluate with the next point on the contour.

          for(let k = 0; k < subject.length - 1; k++) {
            const p = subject.contour2d ? subject.contour2d[k] : subject[k].clone().applyQuaternion(subject.transform)

            const distance = distanceToContour(contour.contour2d, p)
            if(distance < 0) { // inside
              holeIndexes.push(j)
              contour.holes = contour.holes || []
              contour.holes.push(contour.length)
              if(subject.holes) {
                contour.holes.push(...subject.holes.map(offset => offset + contour.length))
              }
              contour.push(...subject)
              break
            } else if(distance > 0) { // outside
              // do nothing, this subject seems to be external to the contour's loop
              break
            } else if(distance === 0) { // on the same contour
              continue
            }
          }
        }
      }

      return contours.filter((_v, i) => !holeIndexes.includes(i) )
    }

    // contour-finding code based on https://stackoverflow.com/a/46811485/2100919
    // heavily modified to permit finding maximal open-ended non-cyclic contours
    var getContours = function(points, contours) {
      let contour = [];

      // find first line for the contour
      let firstPointIndex = 0;
      let secondPointIndex = 0;
      let firstPoint, secondPoint;
      for (let i = 0; i < points.length; i++) {
        if (points[i].checked == true) continue;
        firstPointIndex = i;
        firstPoint = points[firstPointIndex];
        firstPoint.checked = true;
        secondPointIndex = getPairIndex(firstPoint, firstPointIndex, points);
        secondPoint = points[secondPointIndex];
        secondPoint.checked = true;
        contour.push(firstPoint.clone());
        contour.push(secondPoint.clone());
        break;
      }

      contour = getContour(secondPoint, points, contour);
      contours.push(contour);
      let allChecked = 0;
      points.forEach(p => { allChecked += p.checked == true ? 1 : 0; });
      if (allChecked != points.length) { return getContours(points, contours); }
      return contours;
    }

    var getContour = function(currentPoint, points, contour) {
      let p1Index = getNearestPointIndex(currentPoint, points);
      if(p1Index !== 0) { // match found
        let p1 = points[p1Index];
        p1.checked = true;
        let p2Index = getPairIndex(p1, p1Index, points);
        let p2 = points[p2Index];
        p2.checked = true;
        let isClosed = p2.equals(contour[0], 1e-12);
        if (!isClosed) {
          contour.push(p2.clone());
          return getContour(p2, points, contour);
        } else {
          contour.push(contour[0].clone());
          contour.closed = true
          return contour;
        }
      } else {
        return getContourBack(contour[0], points, contour)
      }
    }

    var getContourBack = function(currentPoint, points, contour) {
      let p1Index = getNearestPointIndex(currentPoint, points);
      if(p1Index !== 0) {
        let p1 = points[p1Index];
        p1.checked = true;
        let p2Index = getPairIndex(p1, p1Index, points);
        let p2 = points[p2Index];
        p2.checked = true;
        contour.unshift(p2.clone())
        return getContourBack(contour[0], points, contour)
      } else { // we already know it can't be closed
        contour.closed = false
        return contour
      }
    }

    var getNearestPointIndex = function(point, points){
      let index = 0;
      for (let i = 0; i < points.length; i++){
        let p = points[i];
        if (p.checked !== true && p.equals(point, 1e-12)){ // early exits, not technically 'nearest' point. Nearest would be better, but also slower
          index = i;
          break;
        }
      }
      return index;
    }

    var getPairIndex = function(_point, pointIndex, _points) {
      if (pointIndex % 2 === 0) {
        return pointIndex + 1
      } else {
        return pointIndex - 1
      }
    }
    // end contour-finding code

    var sliceGeometry = function(geometry, plane, closeHoles) {
        var sliced = new THREE.Geometry();
        var builder = new GeometryBuilder(geometry, sliced, plane);

        var distances = [];
        var positions = [];

        geometry.vertices.forEach(function(vertex) {
            var distance = findDistance(vertex, plane);
            var position = distanceAsPosition(distance);
            distances.push(distance);
            positions.push(position);
        });

        geometry.faces.forEach(function(face, faceIndex) {

            var facePositions = FACE_KEYS.map(function(key) {
                return positions[face[key]];
            });

            if (
                facePositions.indexOf(FRONT) === -1 &&
                facePositions.indexOf(BACK) !== -1
            ) {
                return;
            }

            builder.startFace(faceIndex);

            var lastKey = FACE_KEYS[FACE_KEYS.length - 1];
            var lastIndex = face[lastKey];
            var lastDistance = distances[lastIndex];
            var lastPosition = positions[lastIndex];

            FACE_KEYS.map(function(key) {
                var index = face[key];
                var distance = distances[index];
                var position = positions[index];

                if (position === FRONT) {
                    if (lastPosition === BACK) {
                        builder.addIntersection(lastKey, key, lastDistance, distance);
                        builder.addVertex(key);
                    } else {
                        builder.addVertex(key);
                    }
                }

                if (position === ON) {
                    builder.addVertex(key);
                }

                if (position === BACK && lastPosition === FRONT) {
                    builder.addIntersection(lastKey, key, lastDistance, distance);
                }

                lastKey = key;
                lastIndex = index;
                lastPosition = position;
                lastDistance = distance;
            });

            builder.endFace();
        });

        if (closeHoles) {
            builder.closeHoles();
        }

        return sliced;
    };

    var distanceAsPosition = function(distance) {
        if (distance < 0) {
            return BACK;
        }
        if (distance > 0) {
            return FRONT;
        }
        return ON;
    };

    var findDistance = function(vertex, plane) {
        return plane.distanceToPoint(vertex);
    };

    var GeometryBuilder = function(sourceGeometry, targetGeometry, slicePlane) {
        this.sourceGeometry = sourceGeometry;
        this.targetGeometry = targetGeometry;
        this.slicePlane = slicePlane;
        this.addedVertices = [];
        this.addedIntersections = [];
        this.newEdges = [[]];
    };

    GeometryBuilder.prototype.startFace = function(sourceFaceIndex) {
        this.sourceFaceIndex = sourceFaceIndex;
        this.sourceFace = this.sourceGeometry.faces[sourceFaceIndex];
        this.sourceFaceUvs = this.sourceGeometry.faceVertexUvs[0][sourceFaceIndex];

        this.faceIndices = [];
        this.faceNormals = [];
        this.faceUvs = [];
    };

    GeometryBuilder.prototype.endFace = function() {
        var indices = this.faceIndices.map(function(index, i) {
            return i;
        });
        this.addFace(indices);
    };

    GeometryBuilder.prototype.closeHoles = function() {
      if ( ! this.newEdges[0].length) {
          return;
      }

      let contours
      if(this.slicePlane.nonPlanar) {
        // ALGORITHM FOR CLOSING 2D PLANAR EDGE LOOPS FROM POLYGONAL CUT

        // map boundary edges
        //  for every edge, determine which plane is closest (by sum of abs(distance) for endpoints)

        // map planes
        //    find open-ended contours among the points cast to that plane

        // map rays
        //   find all endpoints of unclosed contours closest to each ray
        //   sort points by distance from origin of ray?
        //   find pairs of endpoints (crossings) sorted by distance (0 and 1, 2 and 3, etc)
        //   connect pairs of endpoints
        //   merge contours, reevaluate?

        const planes = this.slicePlane.planes()
        const rays = this.slicePlane.rays()

        contours = []

        let index = [...planes]
        const verticesByPlane = new Map()
        index.forEach(plane => verticesByPlane.set(plane, []))

        this.newEdges.forEach(edge => {
          const begin = this.targetGeometry.vertices[edge[0]]
          const end = this.targetGeometry.vertices[edge[1]]
          index.sort((planeA, planeB) => {
            return (Math.abs(planeA.distanceToPoint(begin)) + Math.abs(planeA.distanceToPoint(end))) - (Math.abs(planeB.distanceToPoint(begin)) + Math.abs(planeB.distanceToPoint(end)))
          })
          verticesByPlane.get(index[0]).push(begin.clone(), end.clone())
        })

        planes.map((plane, planeIndex) => {
          const vertices = verticesByPlane.get(plane)
          if(vertices.length === 0) { return [] } // no edges near this plane

          const planeContours = getContours(vertices, [])
          const quaternion = getTransform(plane)
          planeContours.forEach(contour => {
            contour.transform = quaternion
            contour.normal = plane.normal
          })

          index = [rays[planeIndex], rays[(planeIndex + 1) % rays.length]]
          const unclosedContours = planeContours.filter(contour => !contour.closed)
          const endpointsByRay = new Map()
          index.forEach(ray => endpointsByRay.set(ray, []))
          const contourMap = new Map()

          unclosedContours.flatMap((contour, i) => {
            contour.i = i
            const begin = contour[0]
            const end = contour[contour.length - 1]
            contourMap.set(begin, contour)
            contourMap.set(end, contour)

            return [begin, end]
          }).forEach(point => {
            index.sort((rayA, rayB) => {
              return Math.abs(rayA.distanceToPoint(point)) - Math.abs(rayB.distanceToPoint(point))
            })
            endpointsByRay.get(index[0]).push(point)
          })

          index.map(ray => {

            let endpoints = endpointsByRay.get(ray)
            if(endpoints.length === 0) { return } // no endpoints near this ray

            if(endpoints.length % 2 !== 0) {
              throw new Error('Encountered an odd number of open endpoints. Unable to close contours.')
              console.warn('odd number of crossings, your geometry is out of this world!')
            }

            endpoints = endpoints.sort((a, b) => {
              const origin = ray.origin

              return origin.distanceTo(a) - origin.distanceTo(b)
            })

            for(let i = 0; i < (endpoints.length / 2); i++) {
              const offset = i*2

              const a = endpoints[offset]
              const b = endpoints[offset+1]

              const contourA = contourMap.get(a)
              const contourB = contourMap.get(b)
              console.debug(`contour ${planeIndex}:${contourA.i} meeting ${planeIndex}:${contourB.i}`)
              if(contourA === contourB) {
                if(a === contourA[0]) {
                  contourA.push(a.clone())
                } else {
                  contourA.push(b.clone())
                }
                contourA.closed = true
              } else {
                let reindex
                if(a === contourA[0]) {
                  if(b === contourB[0]) {
                    contourA.unshift(...contourB.reverse())
                    reindex = contourA[0]
                  } else { // b === contourB.last
                    contourA.unshift(...contourB)
                    reindex = contourA[0]
                  }
                } else { // a === contourA.last
                  if(b === contourB[0]) {
                    contourA.push(...contourB)
                    reindex = contourA[contourA.length - 1]
                  } else { // b === contourB.last
                    contourA.push(...contourB.reverse())
                    reindex = contourA[contourA.length - 1]
                  }
                }
                contourA.i = `${contourA.i},${contourB.i}`
                contourMap.set(reindex, contourA)
                planeContours.splice(planeContours.indexOf(contourB), 1)
              }
            }
          })
          const stillUnclosed = planeContours.filter(contour => !contour.closed).length > 0
          if(stillUnclosed) {
            console.warn('unable to close contours')
            throw new Error('unable to close contours')
          }

          const rootContours = associateHoles(planeContours)

          contours.push(...rootContours)
        })
      } else {
        const newVertices = this.newEdges.flat().map(index => this.targetGeometry.vertices[index].clone())
        contours = getContours(newVertices, [])
        const quaternion = getTransform(this.slicePlane)
        contours.forEach(contour => {
          contour.transform = quaternion
          contour.normal = this.slicePlane.normal
        })

        contours = associateHoles(contours)
      }

      // triangulate the closed contours
      contours.forEach(contour => {
        // transform points into the plane of the contour
        const contourVerts = contour.flatMap(v => v.clone().applyQuaternion(contour.transform).toArray() )

        const result = earcut(contourVerts, contour.holes, 3)

        let vertexIndex = this.targetGeometry.vertices.length // to initialize next index
        for(let i = 0; i < (result.length / 3); i++) {
          const offset = i*3
          const a = contour[result[offset]].clone()
          const b = contour[result[offset+1]].clone()
          const c = contour[result[offset+2]].clone()

          var normal = this.faceNormalFromVertices([a, b, c])
          if(normal.dot(contour.normal) > .5) {
            this.targetGeometry.vertices.push(c, b, a)
          } else {
            this.targetGeometry.vertices.push(a, b, c)
          }
          this.targetGeometry.faces.push(
            new THREE.Face3(vertexIndex, vertexIndex + 1, vertexIndex + 2)
          )
          vertexIndex = vertexIndex + 3
        }
      })

      this.targetGeometry.computeFaceNormals()
      return
    };

    GeometryBuilder.prototype.addVertex = function(key) {
        this.addUv(key);
        this.addNormal(key);

        var index = this.sourceFace[key];
        var newIndex;

        if (this.addedVertices.hasOwnProperty(index)) {
            newIndex = this.addedVertices[index];
        } else {
            var vertex = this.sourceGeometry.vertices[index];
            this.targetGeometry.vertices.push(vertex);
            newIndex = this.targetGeometry.vertices.length - 1;
            this.addedVertices[index] = newIndex;
        }
        this.faceIndices.push(newIndex);
    };

    GeometryBuilder.prototype.addIntersection = function(keyA, keyB, distanceA, distanceB) {
        var t = Math.abs(distanceA) / (Math.abs(distanceA) + Math.abs(distanceB));
        this.addIntersectionUv(keyA, keyB, t);
        this.addIntersectionNormal(keyA, keyB, t);

        var indexA = this.sourceFace[keyA];
        var indexB = this.sourceFace[keyB];
        var id = this.intersectionId(indexA, indexB);
        var index;

        if (this.addedIntersections.hasOwnProperty(id)) {
            index = this.addedIntersections[id];
        } else {
            var vertexA = this.sourceGeometry.vertices[indexA];
            var vertexB = this.sourceGeometry.vertices[indexB];
            var newVertex = vertexA.clone().lerp(vertexB, t);
            this.targetGeometry.vertices.push(newVertex);
            index = this.targetGeometry.vertices.length - 1;
            this.addedIntersections[id] = index;
        }
        this.faceIndices.push(index);
        this.updateNewEdges(index);
    };

    GeometryBuilder.prototype.addUv = function(key) {
        if ( ! this.sourceFaceUvs) {
            return;
        }
        var index = this.keyIndex(key);
        var uv = this.sourceFaceUvs[index];
        this.faceUvs.push(uv);
    };

    GeometryBuilder.prototype.addIntersectionUv = function(keyA, keyB, t) {
        if ( ! this.sourceFaceUvs) {
            return;
        }
        var indexA = this.keyIndex(keyA);
        var indexB = this.keyIndex(keyB);
        var uvA = this.sourceFaceUvs[indexA];
        var uvB = this.sourceFaceUvs[indexB];
        var uv = uvA.clone().lerp(uvB, t);
        this.faceUvs.push(uv);
    };

    GeometryBuilder.prototype.addNormal = function(key) {
        if ( ! this.sourceFace.vertexNormals.length) {
            return;
        }
        var index = this.keyIndex(key);
        var normal = this.sourceFace.vertexNormals[index];
        this.faceNormals.push(normal);
    };

    GeometryBuilder.prototype.addIntersectionNormal = function(keyA, keyB, t) {
        if ( ! this.sourceFace.vertexNormals.length) {
            return;
        }
        var indexA = this.keyIndex(keyA);
        var indexB = this.keyIndex(keyB);
        var normalA = this.sourceFace.vertexNormals[indexA];
        var normalB = this.sourceFace.vertexNormals[indexB];
        var normal = normalA.clone().lerp(normalB, t).normalize();
        this.faceNormals.push(normal);
    };

    GeometryBuilder.prototype.addFace = function(indices) {
        if (indices.length === 3) {
            this.addFacePart(indices[0], indices[1], indices[2]);
            return;
        }

        var pairs = [];
        for (var i = 0; i < indices.length; i++) {
            for (var j = i + 1; j < indices.length; j++) {
                var diff = Math.abs(i - j);
                if (diff > 1 && diff < indices.length - 1) {
                    pairs.push([indices[i], indices[j]]);
                }
            }
        }

        pairs.sort(function(pairA, pairB) {
            var lengthA = this.faceEdgeLength(pairA[0], pairA[1]);
            var lengthB = this.faceEdgeLength(pairB[0], pairB[1]);
            return lengthA - lengthB;
        }.bind(this));

        var a = indices.indexOf(pairs[0][0]);
        indices = indices.slice(a).concat(indices.slice(0, a));

        var b = indices.indexOf(pairs[0][1]);
        var indicesA = indices.slice(0, b + 1);
        var indicesB = indices.slice(b).concat(indices.slice(0, 1));

        this.addFace(indicesA);
        this.addFace(indicesB);
    };

    GeometryBuilder.prototype.addFacePart = function(a, b, c) {
        var normals = null;
        if (this.faceNormals.length) {
            normals = [
                this.faceNormals[a],
                this.faceNormals[b],
                this.faceNormals[c],
            ];
        }
        var face = new THREE.Face3(
            this.faceIndices[a],
            this.faceIndices[b],
            this.faceIndices[c],
            normals
        );
        this.targetGeometry.faces.push(face);
        if ( ! this.sourceFaceUvs) {
            return;
        }
        this.targetGeometry.faceVertexUvs[0].push([
            this.faceUvs[a],
            this.faceUvs[b],
            this.faceUvs[c]
        ]);
    };

    GeometryBuilder.prototype.faceEdgeLength = function(a, b) {
        var indexA = this.faceIndices[a];
        var indexB = this.faceIndices[b];
        var vertexA = this.targetGeometry.vertices[indexA];
        var vertexB = this.targetGeometry.vertices[indexB];
        return vertexA.distanceToSquared(vertexB);
    };

    GeometryBuilder.prototype.intersectionId = function(indexA, indexB) {
        return [indexA, indexB].sort().join(',');
    };

    GeometryBuilder.prototype.keyIndex = function(key) {
        return FACE_KEYS.indexOf(key);
    };

    GeometryBuilder.prototype.updateNewEdges = function(index) {
        var edgeIndex = this.newEdges.length - 1;
        var edge = this.newEdges[edgeIndex];
        if (edge.length < 2) {
            edge.push(index);
        } else {
            this.newEdges.push([index]);
        }
    };

    GeometryBuilder.prototype.faceNormal = function(faceIndices) {
        var vertices = faceIndices.map(function(index) {
            return this.targetGeometry.vertices[index];
        }.bind(this));
        return this.faceNormalFromVertices(vertices)
    };

    GeometryBuilder.prototype.faceNormalFromVertices = function(vertices) {
      var edgeA = vertices[0].clone().sub(vertices[1]);
      var edgeB = vertices[0].clone().sub(vertices[2]);
      return edgeA.cross(edgeB).normalize();
    }

    return sliceGeometry;
};
