-- Prove2me | Theorems.Thm_PlanarRot90ScalarSameSideConesDisjoint
-- name    : PlanarRot90ScalarSameSideConesDisjoint
-- status  : Proved
-- author  : @xuanji
-- created : 2026-09-28T01:38:57.102996+00:00
-- url     : https://prove2.me/theorems/5388ac9b-13ae-4a89-baf6-0111b5bd64b5
-- title:
--   Disjointness of scalar same-side quarter-turn cones
-- statement:
--   Let $A,B\in\mathbb R$ and assume that $(A,B)$ is not on the positive $A$-axis, i.e. $
--   eg(0<A\ \wedge\ B=0)$. Then there is a positive constant $\kappa$ such that no two coefficient pairs $(a,b)$ and $(c,r)$ satisfying
--
--   $$
--   a,c>0,\qquad br>0,\qquad |b|<\kappa a,\qquad |r|<\kappa c
--   $$
--
--   can obey the rotated change-of-basis equations
--
--   $$
--   a=cA-rB,\qquad b=cB+rA.
--   $$
--
--   Thus sufficiently narrow same-side scalar cones around the positive $A$-direction are disjoint after the indicated planar rotation. This scalar statement is the coefficient-level core of the geometric cone-disjointness lemma.
-- source:
--   https://github.com/wpegden/crossing-consequences/blob/8769d142033fce042f502bf2857afb6b1375b5c3/Tablet/PlanarRot90ScalarSameSideConesDisjoint.lean#L1-L84

import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Set.Finite.Basic
import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Basic

open Classical
noncomputable section

theorem PlanarRot90ScalarSameSideConesDisjoint (A B : ℝ)
    (hnot : ¬ (0 < A ∧ B = 0)) :
    ∃ κ : ℝ, 0 < κ ∧
      ∀ a c b r : ℝ, 0 < a → 0 < c → 0 < b * r →
        |b| < κ * a → |r| < κ * c →
        ¬ (a = c * A - r * B ∧ b = c * B + r * A) := by sorry
