-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P32_fixedSpectrumExcessRate
-- name    : QAlgorithms.Papers.Independent.Extend50.P32.fixedSpectrumExcessRate
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T09:47:47.846808+00:00
-- url     : https://prove2.me/theorems/cb9c4dcb-3a89-44c0-ae73-99ebd599126d
-- title:
--   Claim 3.9: Fixed-spectrum excess convergence rate
-- statement:
--   Let $d\ge1$ and let $\alpha=(\alpha_1,\ldots,\alpha_d)$ be a nonincreasing probability vector with nonnegative entries. Draw an iid word of length $n$ with letter law $\alpha$ and let $\lambda$ be its weak-insertion RSK shape, padded to $d$ rows. For $1\le k\le d$, write $\lambda_{\le k}=\sum_{i=1}^k\lambda_i$, $\alpha_{\le k}=\sum_{i=1}^k\alpha_i$, $\alpha_{\ge k}=\sum_{i=k}^d\alpha_i$, and $\alpha_{>k}=\sum_{i=k+1}^d\alpha_i$. Here $n\ge0$; every row parameter lies in $[d]$. Write $E_k^{(n)}(\alpha)=\mathbb E\lambda_{\le k}-n\alpha_{\le k}$ and $\operatorname{Excess}_k(\alpha)=\sum_{i\le k<j}\alpha_j/(\alpha_i-\alpha_j)$; a tied cutoff is assigned $+\infty$, whereas the empty sum at $k=d$ is zero. Fix $\alpha$ and $k$ and assume all $\alpha_i$ are distinct. Both the constant and the threshold below may depend on this fixed data.
--
--   $$
--   \exists C_{\alpha,k}>0\ \exists N_{\alpha,k}\ge1\ \forall n\ge N_{\alpha,k}:\quad |E_k^{(n)}(\alpha)-\operatorname{Excess}_k(\alpha)|\le\frac{C_{\alpha,k}}{\sqrt n}.
--   $$
--
--   This quantifies the excess of the leading rows above their linear multinomial scale.
-- source:
--   Efficient quantum tomography II, arXiv:1612.00034v1, PDF p. 15, Claim 3.9

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P32

noncomputable section

open MeasureTheory Filter

open scoped BigOperators ENNReal Matrix ComplexOrder Topology

namespace QAlgorithms.Papers.Independent.Extend50.P32

open QAlgorithms.Papers.Independent.Support50.P38 (wordMass tv)

-- For the density matrices below, the characteristic-polynomial identity
-- preserves all eigenvalues with multiplicity and is equivalent to unitary
-- diagonalization with these real eigenvalues. No accuracy is assumed.

open QAlgorithms.Papers.Independent.Gap20.P17 (HasSpectrum)

/-- Claim 3.9, PDF pp.15-16: constants may depend on the fixed spectrum
and its gaps; k=1 is credited to ITW01. -/
theorem fixedSpectrumExcessRate {d : ℕ} (hd : 0 < d) (alpha : Fin d → ℝ)
    (hAlpha : Learning.IsDistribution alpha) (hSorted : Antitone alpha)
    (hDistinct : Function.Injective alpha) (k : ℕ) (hk : 1 ≤ k) (hkd : k ≤ d) :
    ∃ C : ℝ, 0 < C ∧ ∃ N : ℕ, 1 ≤ N ∧ ∀ n : ℕ, N ≤ n →
      |prefixExcess alpha k n - (spectralPrefixExcessLimit alpha k).toReal| ≤ C / Real.sqrt n := by sorry

end QAlgorithms.Papers.Independent.Extend50.P32

end
