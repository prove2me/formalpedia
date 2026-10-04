-- Prove2me | Theorems.Thm_PolygonalArcEndpointDiskCappedTaperModel
-- name    : PolygonalArcEndpointDiskCappedTaperModel
-- status  : Proved
-- author  : @xuanji
-- created : 2026-09-28T06:34:09.909025+00:00
-- url     : https://prove2.me/theorems/cb37e7ed-42ff-43c3-93af-4482f658f58b
-- title:
--   PolygonalArcEndpointDiskCappedTaperModel
-- statement:
--   A positive-radius, positive-slope endpoint disk-capped taper has open upper and lower regions, each connected and disjoint, while the centerline lies in the taper and removing it splits the taper into those two regions.
-- source:
--   https://github.com/wpegden/crossing-consequences/blob/8769d142033fce042f502bf2857afb6b1375b5c3/Tablet/PolygonalArcEndpointDiskCappedTaperModel.lean#L1-215

import Mathlib.Analysis.Convex.PathConnected
import Mathlib.Analysis.InnerProductSpace.PiL2

open Set

lemma PolygonalArcEndpointDiskCappedTaperModel (a K : ℝ) (ha : 0 < a) (hK : 0 < K) :
    let C : Set (EuclideanSpace ℝ (Fin 2)) :=
      {z | 0 < z 0 ∧ z 0 ^ 2 + z 1 ^ 2 < a ^ 2 ∧ -K * z 0 < z 1 ∧ z 1 < K * z 0}
    let L : Set (EuclideanSpace ℝ (Fin 2)) :=
      {z | 0 < z 0 ∧ z 0 ^ 2 + z 1 ^ 2 < a ^ 2 ∧ 0 < z 1 ∧ z 1 < K * z 0}
    let R : Set (EuclideanSpace ℝ (Fin 2)) :=
      {z | 0 < z 0 ∧ z 0 ^ 2 + z 1 ^ 2 < a ^ 2 ∧ -K * z 0 < z 1 ∧ z 1 < 0}
    let G : Set (EuclideanSpace ℝ (Fin 2)) :=
      {z | 0 < z 0 ∧ z 0 < a ∧ z 1 = 0}
    IsOpen C ∧ IsOpen L ∧ IsOpen R ∧
      IsConnected L ∧ IsConnected R ∧
      Disjoint L R ∧ (0 : EuclideanSpace ℝ (Fin 2)) ∉ C ∧
      G ⊆ C ∧ C \ G = L ∪ R := by sorry
