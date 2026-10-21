-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Next46_P06_semigroup_regularized_norm_structure
-- name    : QAlgorithms.Papers.Independent.Next46.P06.semigroup_regularized_norm_structure
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T13:47:40.394212+00:00
-- url     : https://prove2.me/theorems/be0c271d-a872-45f2-90d2-566af169c274
-- title:
--   §13.2, unnumbered: norm-regularized convergence
-- statement:
--   Let $-A$ generate a bounded semigroup in the paper's positive-time continuity model on a complex Banach space. Put $R=(I+A)^{-1}$ and $\mathcal A=\{R\}'$. For sequences and limits in $\mathcal A$, define
--
--   $$T_n\to_{\tau_A^n}T\iff\exists D\subseteq\mathcal A',\ \bigcap_{d\in D}\ker d=\{0\},\ \forall d\in D,\ \|dT_n-dT\|\to0.$$
--
--   This is an algebraic Hausdorff sequential convergence structure. The operator norm convergence is imposed after multiplication by the common separating family, rather than directly on $T_n$.
-- source:
--   On the Fundamental Principles of Unbounded Functional Calculi, arXiv:2009.04733v1, PDF p. 35, §13.2, unnumbered: norm-regularized convergence

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

/-- Section 13.2, PDF p.35: norm-regularized convergence is an algebraic
Hausdorff convergence structure on A_A. It differs from tau_A^s. -/
theorem semigroup_regularized_norm_structure [CompleteSpace X] (T : ℝ → X →L[ℂ] X)
    (hT : BoundedSemigroup T) (hnd : NondegenerateSemigroup T) :
    let A := negativeGenerator T
    AlgebraicConvergenceOn (regularizedNorm (onePlusInverse A)) (operatorCommutant {onePlusInverse A}) ∧
    HausdorffConvergence (regularizedNorm (onePlusInverse A)) := by sorry

end QAlgorithms.Papers.Independent.Next46.P06

end
