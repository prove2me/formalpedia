-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P32_excessBoundAndLimit
-- name    : QAlgorithms.Papers.Independent.Extend50.P32.excessBoundAndLimit
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T09:36:49.780746+00:00
-- url     : https://prove2.me/theorems/1403e37c-bfd6-4b81-bd82-f2071e9cad8f
-- title:
--   Theorem 1.13: Nonasymptotic excess and its monotone limit
-- statement:
--   Let $d\ge1$ and let $\alpha=(\alpha_1,\ldots,\alpha_d)$ be a nonincreasing probability vector with nonnegative entries. Draw an iid word of length $n$ with letter law $\alpha$ and let $\lambda$ be its weak-insertion RSK shape, padded to $d$ rows. For $1\le k\le d$, write $\lambda_{\le k}=\sum_{i=1}^k\lambda_i$, $\alpha_{\le k}=\sum_{i=1}^k\alpha_i$, $\alpha_{\ge k}=\sum_{i=k}^d\alpha_i$, and $\alpha_{>k}=\sum_{i=k+1}^d\alpha_i$. Here $n\ge0$; every row parameter lies in $[d]$. Write $E_k^{(n)}(\alpha)=\mathbb E\lambda_{\le k}-n\alpha_{\le k}$ and $\operatorname{Excess}_k(\alpha)=\sum_{i\le k<j}\alpha_j/(\alpha_i-\alpha_j)$; a tied cutoff is assigned $+\infty$, whereas the empty sum at $k=d$ is zero.
--
--   $$
--   E_k^{(n)}(\alpha)\le\operatorname{Excess}_k(\alpha):=\sum_{i\le k<j}\frac{\alpha_j}{\alpha_i-\alpha_j}\quad(n\ge0),\qquad E_k^{(n)}(\alpha)\nearrow\operatorname{Excess}_k(\alpha)\quad\text{if all entries are distinct}.
--   $$
--
--   This quantifies the excess of the leading rows above their linear multinomial scale.
-- source:
--   Efficient quantum tomography II, arXiv:1612.00034v1, PDF p. 5, Theorem 1.13

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

/-- Theorem 1.13, PDF p.5: all-n bound and monotone convergence for distinct
entries only. Tied-cutoff excess is extended-valued. -/
theorem excessBoundAndLimit {d : ℕ} (hd : 0 < d) (alpha : Fin d → ℝ)
    (hAlpha : Learning.IsDistribution alpha) (hSorted : Antitone alpha)
    (k : ℕ) (hk : 1 ≤ k) (hkd : k ≤ d) :
    (∀ n : ℕ, ENNReal.ofReal (prefixExcess alpha k n) ≤ spectralPrefixExcessLimit alpha k) ∧
    (Function.Injective alpha → Monotone (prefixExcess alpha k) ∧
      Tendsto (fun n => ENNReal.ofReal (prefixExcess alpha k n)) atTop (𝓝 (spectralPrefixExcessLimit alpha k))) := by sorry

end QAlgorithms.Papers.Independent.Extend50.P32

end
