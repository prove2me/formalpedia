-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P07_relative_entropy_tensor_convex
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P07.relative_entropy_tensor_convex
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T04:36:05.022285+00:00
-- url     : https://prove2.me/theorems/2ddf3cf4-958d-4315-8808-316d1bc97e38
-- title:
--   A.4
-- statement:
--   All quantum systems below are finite-dimensional complex Hilbert spaces of positive dimension, and logarithms are binary. A normalized state is positive semidefinite with trace one; a subnormalized state has trace at most one. Marginals are partial traces. All matrix arguments A,B (and the corresponding second pair in convex combinations) are positive definite; X is an arbitrary rectangular linear map, and convexity is in Loewner order.
--
--   On positive definite operator pairs, (A,B)↦A log A⊗I−A⊗log B is jointly operator convex.
--
--   $$
--   (A,B)\mapsto A\log_2 A\otimes I-A\otimes\log_2 B\text{ is jointly convex}.
--   $$
--
--   This result records the source’s operational or structural relation, with the stated endpoint and attainment clauses retained.
-- source:
--   Quantum Information Processing with Finite Resources -- Mathematical Foundations, arXiv:1504.00233v5, PDF p. 127, A.4

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

/-- NODE paper:1504.00233#A.4
A.4, arXiv:1504.00233v5, PDF p.127. -/
theorem relative_entropy_tensor_convex [Nonempty I] [Nonempty J] (M R : paperMat I) (N S : paperMat J)
    (hM : M.PosDef) (hN : N.PosDef) (hR : R.PosDef) (hS : S.PosDef)
    (l : ℝ) (hl : l ∈ Set.Icc 0 1) :
    paperBelow (Matrix.kronecker (paperMix l M R*matrixLog (paperMix l M R)) (1:paperMat J)-
      Matrix.kronecker (paperMix l M R) (matrixLog (paperMix l N S)))
      (paperMix l (Matrix.kronecker (M*matrixLog M) (1:paperMat J)-Matrix.kronecker M (matrixLog N))
        (Matrix.kronecker (R*matrixLog R) (1:paperMat J)-Matrix.kronecker R (matrixLog S))) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P07

end
