-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Next46_P22_example6
-- name    : QAlgorithms.Papers.Independent.Next46.P22.example6
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-20T13:37:08.930524+00:00
-- url     : https://prove2.me/theorems/d09587d0-2513-4135-b599-24998f787672
-- title:
--   Example 6
-- statement:
--   Let $G$ be any group, $F$ any field and $L=\bigoplus_{g\in G}L^{(g)}$ a $G$-graded $F$-Lie algebra, so $[L^{(g)},L^{(h)}]\subseteq L^{(gh)}$. The coaction constructed from this grading makes $L$ a right $FG$-comodule Lie algebra and satisfies
--
--   $$\rho(a)=a\otimes g\quad(a\in L^{(g)}).$$
--
--   On an arbitrary vector this is the finite sum of its homogeneous components tensor their degrees. The construction uses the given grading and works for infinite or noncommutative groups.
-- source:
--   Structure of H-(co)module Lie algebras, arXiv:1205.0778v7, PDF p. 4, Example 6

import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P22

namespace QAlgorithms.Papers.Independent.Next46.P22

noncomputable section

open scoped TensorProduct

open Classical

section Statements

variable {F H L : Type*} [Field F] [Ring H] [HopfAlgebra F H] [LieRing L] [LieAlgebra F L]

/-- Example 6, PDF p.4: the coaction is the one constructed from the GIVEN grading. -/
theorem example6 {G : Type*} [Group G] (D : Grading F G L) (hD : GradedLie D) :
    ∃ rho : RightComodule F (MonoidAlgebra F G) L,
      (∀ v, rho.rho v = gradedCoaction D v) ∧ ComoduleLie rho ∧
      ∀ g a, Homogeneous D g a → rho.rho a = a ⊗ₜ[F] MonoidAlgebra.single g 1 := by sorry

end Statements

end

end QAlgorithms.Papers.Independent.Next46.P22
