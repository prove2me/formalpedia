-- Prove2me | Theorems.Thm_PolygonalArcInitialEndpointDiskCappedTaperAttachmentStrengthening
-- name    : PolygonalArcInitialEndpointDiskCappedTaperAttachmentStrengthening
-- status  : Proved
-- author  : @xuanji
-- created : 2026-09-28T06:34:27.791994+00:00
-- url     : https://prove2.me/theorems/10bcafc7-9d35-404c-b355-f595c83372d0
-- title:
--   PolygonalArcInitialEndpointDiskCappedTaperAttachmentStrengthening
-- statement:
--   At an initial endpoint, each oriented tube half inside the full control disk is contained in its corresponding disk-capped taper chart image: the left half attaches to the model left region and the right half to the model right region.
-- source:
--   https://github.com/wpegden/crossing-consequences/blob/8769d142033fce042f502bf2857afb6b1375b5c3/Tablet/PolygonalArcInitialEndpointDiskCappedTaperAttachmentStrengthening.lean#L1-156

import Definitions.Def_PlanarRot90
import Definitions.Def_PolygonalArcCollarCompatibleOrientedTubeData

open Set
open Classical
noncomputable section

set_option maxHeartbeats 900000

lemma PolygonalArcInitialEndpointDiskCappedTaperAttachmentStrengthening
    (γ : PolygonalArc) {η : ℝ}
    (controlRadii : PolygonalArcCollarControlRadii γ η)
    (middleSegments : PolygonalArcCollarMiddleSegmentData γ controlRadii)
    (forbiddenMargins :
      PolygonalArcCollarMiddleForbiddenMargins γ controlRadii middleSegments)
    (compatibleTubes :
      PolygonalArcCollarCompatibleOrientedTubeData γ controlRadii middleSegments
        forbiddenMargins)
    (j : ℕ) (hj : j + 1 < γ.vertices.length) :
    let sep := compatibleTubes.orientedTubes.toPolygonalArcCollarSeparatedTubeData
    let d : EuclideanSpace ℝ (Fin 2) := γ.vertices[j + 1] - γ.vertices[j]
    let K : ℝ := compatibleTubes.initialConeBound j hj
    let chart : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2) :=
      fun z => γ.vertices[j] + z 0 • d + z 1 • PlanarRot90 d
    let a : ℝ :=
      controlRadii.radius ⟨j, Nat.lt_of_succ_lt hj⟩ /
        dist γ.vertices[j] γ.vertices[j + 1]
    let L : Set (EuclideanSpace ℝ (Fin 2)) :=
      {z | 0 < z 0 ∧ z 0 ^ 2 + z 1 ^ 2 < a ^ 2 ∧ 0 < z 1 ∧
        z 1 < K * z 0}
    let R : Set (EuclideanSpace ℝ (Fin 2)) :=
      {z | 0 < z 0 ∧ z 0 ^ 2 + z 1 ^ 2 < a ^ 2 ∧ -K * z 0 < z 1 ∧
        z 1 < 0}
    sep.leftHalf j hj ∩
        Metric.ball γ.vertices[j]
          (controlRadii.radius ⟨j, Nat.lt_of_succ_lt hj⟩) ⊆
      chart '' L ∧
    sep.rightHalf j hj ∩
        Metric.ball γ.vertices[j]
          (controlRadii.radius ⟨j, Nat.lt_of_succ_lt hj⟩) ⊆
      chart '' R := by sorry
