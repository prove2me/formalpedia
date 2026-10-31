-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P07_lieb_ando_tensor
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P07.lieb_ando_tensor
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T04:35:24.583321+00:00
-- url     : https://prove2.me/theorems/656a70e4-9212-4847-a9bf-a656d8a9d11c
-- title:
--   A.3
-- statement:
--   All quantum systems below are finite-dimensional complex Hilbert spaces of positive dimension, and logarithms are binary. A normalized state is positive semidefinite with trace one; a subnormalized state has trace at most one. Marginals are partial traces. All matrix arguments A,B (and the corresponding second pair in convex combinations) are positive definite; X is an arbitrary rectangular linear map, and convexity is in Loewner order.
--
--   (A,B)↦A^α⊗B^(1−α) on positive definite operators is jointly operator concave for 0<α<1 and jointly operator convex for −1<α<0 or 1<α<2.
--
--   $$
--   (A,B)\mapsto A^\alpha\otimes B^{1-\alpha}\text{ is jointly concave for }0<\alpha<1\text{ and jointly convex for }\alpha\in(-1,0)\cup(1,2).
--   $$
--
--   This result records the source’s operational or structural relation, with the stated endpoint and attainment clauses retained.
-- source:
--   Quantum Information Processing with Finite Resources -- Mathematical Foundations, arXiv:1504.00233v5, PDF p. 126, A.3

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P07

noncomputable section

open Filter

open scoped BigOperators Matrix ComplexConjugate ComplexOrder Matrix.Norms.L2Operator Topology

namespace QAlgorithms.Papers.Independent.Intakenext100.P07

attribute [local instance] Classical.propDecidable Classical.decEq

variable {I J A B C D X Y Z : Type*}

variable [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]

variable [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]

variable [Fintype C] [DecidableEq C] [Fintype D] [DecidableEq D]

variable [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]

variable [Fintype Z] [DecidableEq Z]

/-- NODE paper:1504.00233#A.3
A.3, arXiv:1504.00233v5, PDF p.126. -/
theorem lieb_ando_tensor [Nonempty I] [Nonempty J] (M R : paperMat I) (N S : paperMat J)
    (hM : M.PosDef) (hN : N.PosDef) (hR : R.PosDef) (hS : S.PosDef)
    (l : ℝ) (hl : l ∈ Set.Icc 0 1) (a : ℝ) :
    (0 < a → a < 1 → paperBelow (paperMix l (Matrix.kronecker (paperPower M a) (paperPower N (1-a)))
      (Matrix.kronecker (paperPower R a) (paperPower S (1-a)))) (Matrix.kronecker (paperPower (paperMix l M R) a) (paperPower (paperMix l N S) (1-a)))) ∧
    ((-1 < a ∧ a < 0) ∨ (1 < a ∧ a < 2) → paperBelow (Matrix.kronecker (paperPower (paperMix l M R) a) (paperPower (paperMix l N S) (1-a)))
      (paperMix l (Matrix.kronecker (paperPower M a) (paperPower N (1-a))) (Matrix.kronecker (paperPower R a) (paperPower S (1-a))))) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P07

end
