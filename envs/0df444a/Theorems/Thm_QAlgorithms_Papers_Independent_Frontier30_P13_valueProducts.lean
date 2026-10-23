-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Frontier30_P13_valueProducts
-- name    : QAlgorithms.Papers.Independent.Frontier30.P13.valueProducts
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-19T09:17:30.995986+00:00
-- url     : https://prove2.me/theorems/323a90d0-7651-441d-86b1-960d1aa8b724
-- title:
--   The value of a finite Gaussian tensor product is the minimum factor value
-- statement:
--   Let $K$ be a nonempty finite index set. For each $k\in K$, let $\gamma_k$ be a physical Gaussian covariance on $a_k$ modes held by $A$ and $b_k$ modes held by $B$, where $a_k,b_k\ge1$. Let $\Gamma$ be their direct sum, permuted so that all $A$ modes precede all $B$ modes, and evaluate $V$ across that combined bipartition. Here $V(\gamma)$ is the largest $p\in[0,1]$ such that $\gamma\succeq p(\gamma_A\oplus\gamma_B)$ for physical local covariances. Then
--
--   $$V(\Gamma)=\min_{k\in K}V(\gamma_k).$$
--
--   The minimum is attained at a factor. In particular, adjoining any positive finite number of identical copies leaves this value unchanged.
-- source:
--   The characterization of Gaussian operations and Distillation of Gaussian States, arXiv:quant-ph/0204085v4, PDF p. 6, Appendix A(1), Eq.(A2): V of a tensor product

import Definitions.Def_QAlgorithms_Papers_Independent_Frontier30_P13

noncomputable section

open Filter

open QAlgorithms.Papers.Independent.Dependency50.P10 (complexify physicalCovariance)

open scoped ComplexOrder

attribute [local instance] Classical.decEq

attribute [local instance] Classical.propDecidable

namespace QAlgorithms.Papers.Independent.Frontier30.P13

/-- Appendix A, PDF p.6, Eq.(A2) and its finite-family extension: V of a
nonempty tensor product is the minimum of the factor values, after explicitly
regrouping along the joint A|B partition. -/
theorem valueProducts {K : Type*} [Fintype K] [Nonempty K]
    (a b : K → ℕ) (ha : ∀ k, 0 < a k) (hb : ∀ k, 0 < b k)
    (G : ∀ k, Matrix (BipPhase (Fin (a k)) (Fin (b k)))
      (BipPhase (Fin (a k)) (Fin (b k))) ℝ)
    (hG : ∀ k, physicalCovariance (G k) (bipJ (Fin (a k)) (Fin (b k)))) :
    ∃ k : K, valueV (familyCM a b G) = valueV (G k) ∧
      ∀ l : K, valueV (G k) ≤ valueV (G l) := by sorry

end QAlgorithms.Papers.Independent.Frontier30.P13

end
