-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P21_finiteTruncationSeparation
-- name    : QAlgorithms.Papers.Independent.Information100.P21.finiteTruncationSeparation
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T10:07:09.685526+00:00
-- url     : https://prove2.me/theorems/91d78733-2b56-4478-b9a8-abc1216c1330
-- title:
--   V.C — explicit finite-truncation deduction
-- statement:
--   For $N\ge1$, let $d_j=[\sqrt j\log(j+1)]^{-1}$, $c_N=\sum_{j=1}^Nd_j^2$, and $(H_N)_{jk}=1/(j-k)$ off the diagonal and zero on it. Define
--   $$\rho_{\pm,N}=c_N^{-1}\sum_{j,k=1}^Nd_jd_k\bigl(\delta_{jk}\pm i(H_N)_{jk}/\pi\bigr)|jj\rangle\langle kk|.$$
--   These are density operators with separable sum, so generalized robustness is at most one. Standard robustness is at least $(\pi c_N)^{-1}\sum_{j<k}d_jd_k/(k-j)$, which tends to infinity. Some finite truncation therefore separates the measures. Lean shifts the one-based indices by one; the construction and Hilbert norm bound are credited to Ref. [9].
--
--   PDF p.18: retain the exact negativity identity, not only the standard-robustness lower bound.
-- source:
--   The Minimal Dimension of Entangled -Noise Advantage, arXiv:2609.28367v1, PDF p. 18, V.C — explicit finite-truncation deduction

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P21

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder ENNReal

namespace QAlgorithms.Papers.Independent.Information100.P21

attribute [local instance] Classical.propDecidable Classical.decEq

/-- arxiv:2609.28367v1, PDF p. 18, explicit finite-truncation deduction.
Round-one coverage restoration: PDF p.18: retain the exact negativity identity, not only the standard-robustness lower bound. -/
theorem finiteTruncationSeparation  :
  (∀ N : ℕ, 0<N →
    QAlgorithms.IsDensityMatrix (truncRho N true) ∧ QAlgorithms.IsDensityMatrix (truncRho N false) ∧
    QAlgorithms.Entanglement.IsSeparablePositive (truncRho N true+truncRho N false) ∧
    (∀ plus : Bool, rg (truncRho N plus)≤1 ∧
      QAlgorithms.Entanglement.negativity (truncRho N plus) = truncLower N ∧
      truncLower N≤rs (truncRho N plus))) ∧
  Filter.Tendsto truncLower Filter.atTop Filter.atTop ∧
  (∃ N : ℕ, 0<N ∧ ∀ plus : Bool, rg (truncRho N plus)<rs (truncRho N plus)) := by sorry

end QAlgorithms.Papers.Independent.Information100.P21

end
