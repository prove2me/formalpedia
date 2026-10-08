-- Prove2me | Theorems.Thm_PolygonalArcTerminalEndpointDiskCappedTaperSideLabelling
-- name    : PolygonalArcTerminalEndpointDiskCappedTaperSideLabelling
-- status  : Proved
-- author  : @xuanji
-- created : 2026-09-28T06:34:25.090675+00:00
-- url     : https://prove2.me/theorems/e353d491-308c-42cf-a32c-42f022c85180
-- title:
--   PolygonalArcTerminalEndpointDiskCappedTaperSideLabelling
-- statement:
--   For every polygonal-arc segment, the terminal endpoint disk-capped taper chart labels the oriented tube sides in the reversed orientation: the oriented left half lies in the model right region and the oriented right half lies in the model left region, together with the transported topology and endpoint properties.
-- source:
--   https://github.com/wpegden/crossing-consequences/blob/8769d142033fce042f502bf2857afb6b1375b5c3/Tablet/PolygonalArcTerminalEndpointDiskCappedTaperSideLabelling.lean#L1-242

import Definitions.Def_PlanarRot90
import Definitions.Def_PolygonalArcCollarCompatibleOrientedTubeData

open Set
open Classical
noncomputable section

set_option maxHeartbeats 900000

lemma PolygonalArcTerminalEndpointDiskCappedTaperSideLabelling
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
    let C : Set (EuclideanSpace ℝ (Fin 2)) :=
      {z | 0 < z 0 ∧ z 0 ^ 2 + z 1 ^ 2 < a ^ 2 ∧ -K * z 0 < z 1 ∧
        z 1 < K * z 0}
    let L : Set (EuclideanSpace ℝ (Fin 2)) :=
      {z | 0 < z 0 ∧ z 0 ^ 2 + z 1 ^ 2 < a ^ 2 ∧ 0 < z 1 ∧
        z 1 < K * z 0}
    let R : Set (EuclideanSpace ℝ (Fin 2)) :=
      {z | 0 < z 0 ∧ z 0 ^ 2 + z 1 ^ 2 < a ^ 2 ∧ -K * z 0 < z 1 ∧
        z 1 < 0}
    let G : Set (EuclideanSpace ℝ (Fin 2)) :=
      {z | 0 < z 0 ∧ z 0 < a ∧ z 1 = 0}
    0 < a ∧
      IsOpen C ∧ IsOpen L ∧ IsOpen R ∧
      IsConnected L ∧ IsConnected R ∧
      IsConnected (chart '' L) ∧ IsConnected (chart '' R) ∧
      Disjoint L R ∧ Disjoint (chart '' L) (chart '' R) ∧
      (0 : EuclideanSpace ℝ (Fin 2)) ∉ C ∧ G ⊆ C ∧ C \ G = L ∪ R ∧
      (∀ z : EuclideanSpace ℝ (Fin 2),
        z 0 ^ 2 + z 1 ^ 2 < a ^ 2 →
          chart z ∈
            Metric.ball γ.vertices[j + 1] (controlRadii.radius ⟨j + 1, hj⟩)) ∧
      chart '' C ⊆
        Metric.ball γ.vertices[j + 1] (controlRadii.radius ⟨j + 1, hj⟩) ∧
      γ.vertices[j + 1] ∉ chart '' C ∧
      (∀ {t : ℝ}, 0 < t →
        chart (WithLp.toLp 2 (fun i : Fin 2 => if i = 0 then t else 0)) ≠
          γ.vertices[j + 1]) ∧
      ((AffineMap.lineMap γ.vertices[j] γ.vertices[j + 1]) ''
          Set.Ioo
            (1 - controlRadii.radius ⟨j + 1, hj⟩ /
              dist γ.vertices[j] γ.vertices[j + 1]) (1 : ℝ) ⊆
        chart '' G) ∧
      chart '' C \ chart '' G = chart '' L ∪ chart '' R ∧
      sep.leftHalf j hj ∩ chart '' C ⊆ chart '' R ∧
      sep.rightHalf j hj ∩ chart '' C ⊆ chart '' L := by sorry
