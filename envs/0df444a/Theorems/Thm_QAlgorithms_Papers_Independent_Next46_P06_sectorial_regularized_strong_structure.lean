-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Next46_P06_sectorial_regularized_strong_structure
-- name    : QAlgorithms.Papers.Independent.Next46.P06.sectorial_regularized_strong_structure
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-20T13:46:25.478323+00:00
-- url     : https://prove2.me/theorems/b9129c09-0d2a-41b1-b0ba-45bfb96454fc
-- title:
--   Lemma 11.1
-- statement:
--   Let $A$ be a sectorial operator on a complex Banach space $X$, with no injectivity or dense-domain assumption. Put $R=(I+A)^{-1}$ and $\mathcal A=\{R\}'$, where a prime denotes the bounded-operator commutant. For sequences and limits in $\mathcal A$, define
--
--   $$T_n\to_{\tau_A^s}T\iff\exists D\subseteq\mathcal A',\ \bigcap_{d\in D}\ker d=\{0\},\ \forall d\in D\ \forall x\in X,\ dT_nx\to dTx.$$
--
--   This relation is an algebraic Hausdorff sequential convergence structure on $\mathcal A$. The convergence occurs after multiplying by a common separating family.
-- source:
--   On the Fundamental Principles of Unbounded Functional Calculi, arXiv:2009.04733v1, PDF p. 27, Lemma 11.1

import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P06

noncomputable section

attribute [local instance] Classical.propDecidable

open Set Filter

open scoped Topology

namespace QAlgorithms.Papers.Independent.Next46.P06

open QAlgorithms.Papers.Independent.Claimed50.P05 (graphDomain GraphCore)

universe u v w

variable {F G : Type*} [Ring F] [Algebra ℂ F] [Ring G] [Algebra ℂ G]

variable {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
  [NormedAddCommGroup Y] [NormedSpace ℂ Y] [CompleteSpace Y]

/-- Lemma 11.1, PDF p.27: the specified regularized-strong relation on the
resolvent operatorCommutant is algebraic and Hausdorff. -/
theorem sectorial_regularized_strong_structure [CompleteSpace X] (A : Graph X) (hA : Sectorial A) :
    AlgebraicConvergenceOn (regularizedStrong (onePlusInverse A)) (operatorCommutant {onePlusInverse A}) ∧
    HausdorffConvergence (regularizedStrong (onePlusInverse A)) := by sorry

end QAlgorithms.Papers.Independent.Next46.P06

end
