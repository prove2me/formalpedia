-- Prove2me | Theorems.Thm_PolygonalArcSideStripSetAlgebra
-- name    : PolygonalArcSideStripSetAlgebra
-- status  : Proved
-- author  : @xuanji
-- created : 2026-09-28T05:03:35.074379+00:00
-- url     : https://prove2.me/theorems/91ced734-45c7-4924-93a9-0ff9fd407844
-- title:
--   Set algebra for assembled polygonal-arc side strips
-- statement:
--   Given the middle tubes, vertex collars, and local side pieces, define the global collar and its left and right strips by union. Then each strip is disjoint from the arc, the two strips are disjoint from each other, and deleting the relative interior of the arc from the collar gives exactly the union of the two strips.
-- source:
--   https://github.com/wpegden/crossing-consequences/blob/8769d142033fce042f502bf2857afb6b1375b5c3/Tablet/PolygonalArcSideStripSetAlgebra.lean#L1-L33

import Definitions.Def_PolygonalArcCollarLocalSideData

open Classical
noncomputable section

lemma PolygonalArcSideStripSetAlgebra
    (γ : PolygonalArc) {η : ℝ}
    (controlRadii : PolygonalArcCollarControlRadii γ η)
    (middleSegments : PolygonalArcCollarMiddleSegmentData γ controlRadii)
    (forbiddenMargins :
      PolygonalArcCollarMiddleForbiddenMargins γ controlRadii middleSegments)
    (orientedTubes : PolygonalArcCollarOrientedSeparatedTubeData γ controlRadii middleSegments
        forbiddenMargins)
    (vertexLocalPieces :
      PolygonalArcCollarVertexLocalPieceData γ controlRadii middleSegments
        forbiddenMargins orientedTubes.toPolygonalArcCollarSeparatedTubeData)
    (localSideData :
      PolygonalArcCollarLocalSideData γ controlRadii middleSegments
        forbiddenMargins orientedTubes vertexLocalPieces) :
    let sep := orientedTubes.toPolygonalArcCollarSeparatedTubeData
    let C : Set (EuclideanSpace ℝ (Fin 2)) :=
      ((⋃ (j : ℕ), ⋃ (hj : j + 1 < γ.vertices.length), sep.tube j hj) ∪
        (⋃ i : Fin γ.vertices.length, localSideData.vertexCollar i))
    let L : Set (EuclideanSpace ℝ (Fin 2)) :=
      ((⋃ (j : ℕ), ⋃ (hj : j + 1 < γ.vertices.length), sep.leftHalf j hj) ∪
        (⋃ i : Fin γ.vertices.length, localSideData.leftSidePiece i))
    let R : Set (EuclideanSpace ℝ (Fin 2)) :=
      ((⋃ (j : ℕ), ⋃ (hj : j + 1 < γ.vertices.length), sep.rightHalf j hj) ∪
        (⋃ i : Fin γ.vertices.length, localSideData.rightSidePiece i))
    Disjoint L γ.carrier ∧ Disjoint R γ.carrier ∧ Disjoint L R ∧
      C \ γ.relativeInterior = L ∪ R := by sorry
