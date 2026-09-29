-- Prove2me | Theorems.Thm_PolygonalArcTerminalEndpointDiskCappedTaperAttachmentStrengthening
-- name    : PolygonalArcTerminalEndpointDiskCappedTaperAttachmentStrengthening
-- status  : Open
-- author  : @xuanji
-- created : 2026-09-28T06:34:31.362531+00:00
-- url     : https://prove2.me/theorems/5151dc37-ede5-47e5-8408-12af8cedebc8
-- title:
--   PolygonalArcTerminalEndpointDiskCappedTaperAttachmentStrengthening
-- statement:
--   At a terminal endpoint, each oriented tube half inside the full control disk is contained in the correspondingly reversed disk-capped taper chart image: the left half attaches to the model right region and the right half to the model left region.
-- source:
--   https://github.com/wpegden/crossing-consequences/blob/8769d142033fce042f502bf2857afb6b1375b5c3/Tablet/PolygonalArcTerminalEndpointDiskCappedTaperAttachmentStrengthening.lean#L1-161

import Definitions.Def_PlanarRot90
import Definitions.Def_PolygonalArcCollarCompatibleOrientedTubeData

open Set
open Classical
noncomputable section

set_option maxHeartbeats 900000

lemma PolygonalArcTerminalEndpointDiskCappedTaperAttachmentStrengthening
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
    let d : EuclideanSpace ℝ (Fin 2) := γ.vertices[j] - γ.vertices[j + 1]
    let K : ℝ := compatibleTubes.terminalConeBound j hj
    let chart : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2) :=
      fun z => γ.vertices[j + 1] + z 0 • d + z 1 • PlanarRot90 d
    let a : ℝ :=
      controlRadii.radius ⟨j + 1, hj⟩ /
        dist γ.vertices[j + 1] γ.vertices[j]
    let L : Set (EuclideanSpace ℝ (Fin 2)) :=
      {z | 0 < z 0 ∧ z 0 ^ 2 + z 1 ^ 2 < a ^ 2 ∧ 0 < z 1 ∧
        z 1 < K * z 0}
    let R : Set (EuclideanSpace ℝ (Fin 2)) :=
      {z | 0 < z 0 ∧ z 0 ^ 2 + z 1 ^ 2 < a ^ 2 ∧ -K * z 0 < z 1 ∧
        z 1 < 0}
    sep.leftHalf j hj ∩
        Metric.ball γ.vertices[j + 1] (controlRadii.radius ⟨j + 1, hj⟩) ⊆
      chart '' R ∧
    sep.rightHalf j hj ∩
        Metric.ball γ.vertices[j + 1] (controlRadii.radius ⟨j + 1, hj⟩) ⊆
      chart '' L := by sorry
