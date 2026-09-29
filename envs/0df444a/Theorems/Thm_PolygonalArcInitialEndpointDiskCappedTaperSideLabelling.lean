-- Prove2me | Theorems.Thm_PolygonalArcInitialEndpointDiskCappedTaperSideLabelling
-- name    : PolygonalArcInitialEndpointDiskCappedTaperSideLabelling
-- status  : Open
-- author  : @xuanji
-- created : 2026-09-28T06:34:22.083984+00:00
-- url     : https://prove2.me/theorems/3327d970-9c13-463b-a642-a3ab81b1f12a
-- title:
--   PolygonalArcInitialEndpointDiskCappedTaperSideLabelling
-- statement:
--   For every polygonal-arc segment, the initial endpoint disk-capped taper chart labels the oriented tube sides: within the charted taper, the oriented left half lies in the model left region and the oriented right half lies in the model right region, in addition to the chart-transport topology and endpoint properties.
-- source:
--   https://github.com/wpegden/crossing-consequences/blob/8769d142033fce042f502bf2857afb6b1375b5c3/Tablet/PolygonalArcInitialEndpointDiskCappedTaperSideLabelling.lean#L1-206

import Definitions.Def_PlanarRot90
import Definitions.Def_PolygonalArcCollarCompatibleOrientedTubeData

open Set
open Classical
noncomputable section

set_option maxHeartbeats 900000

lemma PolygonalArcInitialEndpointDiskCappedTaperSideLabelling
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
          chart z ∈ Metric.ball γ.vertices[j]
            (controlRadii.radius ⟨j, Nat.lt_of_succ_lt hj⟩)) ∧
      chart '' C ⊆ Metric.ball γ.vertices[j]
        (controlRadii.radius ⟨j, Nat.lt_of_succ_lt hj⟩) ∧
      γ.vertices[j] ∉ chart '' C ∧
      (∀ {t : ℝ}, 0 < t →
        chart (WithLp.toLp 2 (fun i : Fin 2 => if i = 0 then t else 0)) ≠
          γ.vertices[j]) ∧
      ((AffineMap.lineMap γ.vertices[j] γ.vertices[j + 1]) '' Set.Ioo (0 : ℝ) a ⊆
        chart '' G) ∧
      chart '' C \ chart '' G = chart '' L ∪ chart '' R ∧
      sep.leftHalf j hj ∩ chart '' C ⊆ chart '' L ∧
      sep.rightHalf j hj ∩ chart '' C ⊆ chart '' R := by sorry
