-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P07_schur_complement
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P07.schur_complement
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T04:34:17.437996+00:00
-- url     : https://prove2.me/theorems/43deb751-7540-4966-a891-3e78a814d329
-- title:
--   A.1
-- statement:
--   All quantum systems below are finite-dimensional complex Hilbert spaces of positive dimension, and logarithms are binary. A normalized state is positive semidefinite with trace one; a subnormalized state has trace at most one. Marginals are partial traces. All matrix arguments A,B (and the corresponding second pair in convex combinations) are positive definite; X is an arbitrary rectangular linear map, and convexity is in Loewner order.
--
--   For finite positive definite A,B and arbitrary rectangular X, block [[A,X],[X†,B]] is PSD iff A≥X B^{-1}X†.
--
--   $$
--   \begin{pmatrix}A&X\\X^\dagger&B\end{pmatrix}\ge0\quad\Longleftrightarrow\quad A\ge XB^{-1}X^\dagger.
--   $$
--
--   This result records the source’s operational or structural relation, with the stated endpoint and attainment clauses retained.
-- source:
--   Quantum Information Processing with Finite Resources -- Mathematical Foundations, arXiv:1504.00233v5, PDF p. 125, A.1

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

/-- NODE paper:1504.00233#A.1
A.1, arXiv:1504.00233v5, PDF p.125. -/
theorem schur_complement [Nonempty I] [Nonempty J] (M : paperMat I) (N : paperMat J) (X : Matrix I J ℂ)
    (hM : M.PosDef) (hN : N.PosDef) : (Matrix.fromBlocks M X Xᴴ N).PosSemidef ↔ paperBelow (X*N⁻¹*Xᴴ) M := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P07

end
