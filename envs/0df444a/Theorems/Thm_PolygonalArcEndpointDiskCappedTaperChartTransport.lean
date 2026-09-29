-- Prove2me | Theorems.Thm_PolygonalArcEndpointDiskCappedTaperChartTransport
-- name    : PolygonalArcEndpointDiskCappedTaperChartTransport
-- status  : Open
-- author  : @xuanji
-- created : 2026-09-28T06:34:17.974979+00:00
-- url     : https://prove2.me/theorems/1fd11df1-6571-454f-8468-90a40939ca7e
-- title:
--   PolygonalArcEndpointDiskCappedTaperChartTransport
-- statement:
--   For two distinct points and positive radius and slope parameters, the affine chart built from the segment and its quarter-turn transports the endpoint taper model into the corresponding metric disk: it preserves openness, connectedness, disjointness, the centerline split, and the endpoint and disk-containment properties.
-- source:
--   https://github.com/wpegden/crossing-consequences/blob/8769d142033fce042f502bf2857afb6b1375b5c3/Tablet/PolygonalArcEndpointDiskCappedTaperChartTransport.lean#L1-224

import Definitions.Def_PlanarRot90

open Set
open Classical
noncomputable section

lemma PolygonalArcEndpointDiskCappedTaperChartTransport
    (p0 p1 : EuclideanSpace ℝ (Fin 2)) (r K : ℝ)
    (hp : p1 ≠ p0) (hr : 0 < r) (hK : 0 < K) :
    let d : EuclideanSpace ℝ (Fin 2) := p1 - p0
    let chart : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2) :=
      fun z => p0 + z 0 • d + z 1 • PlanarRot90 d
    let a : ℝ := r / dist p0 p1
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
        z 0 ^ 2 + z 1 ^ 2 < a ^ 2 → chart z ∈ Metric.ball p0 r) ∧
      chart '' C ⊆ Metric.ball p0 r ∧
      p0 ∉ chart '' C ∧
      (∀ {t : ℝ}, 0 < t →
        chart (WithLp.toLp 2 (fun i : Fin 2 => if i = 0 then t else 0)) ≠ p0) ∧
      ((AffineMap.lineMap p0 p1) '' Set.Ioo (0 : ℝ) a ⊆ chart '' G) ∧
      chart '' C \ chart '' G = chart '' L ∪ chart '' R := by sorry
