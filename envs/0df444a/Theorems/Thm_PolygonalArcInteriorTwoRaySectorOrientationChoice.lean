-- Prove2me | Theorems.Thm_PolygonalArcInteriorTwoRaySectorOrientationChoice
-- name    : PolygonalArcInteriorTwoRaySectorOrientationChoice
-- status  : Proved
-- author  : @moona3k
-- created : 2026-10-04T18:41:25.966827+00:00
-- url     : https://prove2.me/theorems/d4c2cc6e-2d7c-4817-ab14-cfd0f1fa27c7
-- title:
--   Polygonal Arc Interior Two Ray Sector Orientation Choice
-- statement:
--   [Two-ray orientation choice]
--   Let $u,v\in\mathbb R^2$ be nonzero vectors, and suppose that $v$ is not
--   a positive scalar multiple of $u$.  Write
--   $$
--     v=c\,u+s\,\operatorname{rot}_{90}(u)
--   $$
--   using the orthogonal frame $(u,\operatorname{rot}_{90}(u))$, with
--   $$
--     c=\frac{\langle v,u\rangle}{\|u\|^2},\qquad
--     s=\frac{\langle v,\operatorname{rot}_{90}(u)\rangle}{\|u\|^2}.
--   $$
--   Then either this $u$-frame already has the second ray in the upper or
--   straight-through-opposite position,
--   $$
--     s>0\quad\text{or}\quad (s=0\text{ and }c<0),
--   $$
--   or, after swapping the two rays and writing
--   $$
--     u=c'\,v+s'\,\operatorname{rot}_{90}(v),
--   $$
--   one has $s'>0$.
--
--   **Formalization Note** This node is ported from the Trellis formalization of the crossing lemma and its consequences ([wpegden/crossing-consequences](https://github.com/wpegden/crossing-consequences), commit `8769d142`, W. Pegden, Apache-2.0); the statement is the Trellis node `PolygonalArcInteriorTwoRaySectorOrientationChoice`.
-- source:
--   https://github.com/wpegden/crossing-consequences/blob/8769d142033fce042f502bf2857afb6b1375b5c3/Tablet/PolygonalArcInteriorTwoRaySectorOrientationChoice.lean#L1-L55

import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Set.Finite.Basic
import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Basic
import Definitions.Def_PlanarRot90

open Classical
noncomputable section

lemma PolygonalArcInteriorTwoRaySectorOrientationChoice {u v : EuclideanSpace ℝ (Fin 2)}
    (hu : u ≠ 0) (hv : v ≠ 0)
    (hnot_same : ¬ ∃ t : ℝ, 0 < t ∧ v = t • u) :
    (let c : ℝ := inner ℝ v u / (‖u‖ ^ 2)
     let s : ℝ := inner ℝ v (PlanarRot90 u) / (‖u‖ ^ 2)
     v = c • u + s • PlanarRot90 u ∧ (0 < s ∨ s = 0 ∧ c < 0)) ∨
    (let c : ℝ := inner ℝ u v / (‖v‖ ^ 2)
     let s : ℝ := inner ℝ u (PlanarRot90 v) / (‖v‖ ^ 2)
     u = c • v + s • PlanarRot90 v ∧ 0 < s) := by sorry
