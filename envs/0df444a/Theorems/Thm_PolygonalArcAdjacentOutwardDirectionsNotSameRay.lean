-- Prove2me | Theorems.Thm_PolygonalArcAdjacentOutwardDirectionsNotSameRay
-- name    : PolygonalArcAdjacentOutwardDirectionsNotSameRay
-- status  : Proved
-- author  : @xuanji
-- created : 2026-09-28T00:51:30.168632+00:00
-- url     : https://prove2.me/theorems/cacdec52-b7ef-4c39-b195-69dbf0911507
-- title:
--   Adjacent polygonal-arc outward directions are not the same positive ray
-- statement:
--   Let $\gamma$ be a simple polygonal arc, and let $i$ be an interior vertex index. The two vectors pointing outward from the vertex along the adjacent segments cannot lie on the same positive ray, in either orientation. Equivalently, neither outward direction is a positive scalar multiple of the other.
--
--   This local nondegeneracy property prevents two consecutive segments from reversing along one line and is the geometric input needed to construct narrow endpoint and junction cones.
-- source:
--   https://github.com/wpegden/crossing-consequences/blob/8769d142033fce042f502bf2857afb6b1375b5c3/Tablet/PolygonalArcAdjacentOutwardDirectionsNotSameRay.lean#L1-L95

import Definitions.Def_PolygonalArc

open Classical
noncomputable section

theorem PolygonalArcAdjacentOutwardDirectionsNotSameRay (γ : PolygonalArc)
    {i : ℕ} (hprev : 0 < i) (hnext : i + 1 < γ.vertices.length) :
    (¬ ∃ a : ℝ, 0 < a ∧
        γ.vertices[i - 1] - γ.vertices[i] =
          a • (γ.vertices[i + 1] - γ.vertices[i])) ∧
      ¬ ∃ a : ℝ, 0 < a ∧
        γ.vertices[i + 1] - γ.vertices[i] =
          a • (γ.vertices[i - 1] - γ.vertices[i]) := by sorry
