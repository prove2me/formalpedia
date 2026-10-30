-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P32_prefixExcessMonotone
-- name    : QAlgorithms.Papers.Independent.Extend50.P32.prefixExcessMonotone
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T09:43:22.97469+00:00
-- url     : https://prove2.me/theorems/207ec918-cd51-4270-a939-4e6407197645
-- title:
--   Lemma 2.5: Monotonicity of expected prefix excess
-- statement:
--   Let $d\ge1$ and let $\alpha=(\alpha_1,\ldots,\alpha_d)$ be a nonincreasing probability vector with nonnegative entries. Draw an iid word of length $n$ with letter law $\alpha$ and let $\lambda$ be its weak-insertion RSK shape, padded to $d$ rows. For $1\le k\le d$, write $\lambda_{\le k}=\sum_{i=1}^k\lambda_i$, $\alpha_{\le k}=\sum_{i=1}^k\alpha_i$, $\alpha_{\ge k}=\sum_{i=k}^d\alpha_i$, and $\alpha_{>k}=\sum_{i=k+1}^d\alpha_i$. Here $n\ge0$; every row parameter lies in $[d]$.
--
--   $$
--   n\longmapsto E_k^{(n)}(\alpha):=\mathbb E\lambda_{\le k}-n\alpha_{\le k}\quad\text{is nondecreasing on }\mathbb N.
--   $$
--
--   This quantifies the excess of the leading rows above their linear multinomial scale.
-- source:
--   Efficient quantum tomography II, arXiv:1612.00034v1, PDF p. 11, Lemma 2.5

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

/-- Lemma 2.5, PDF pp.11-12: UNnormalized excess is nondecreasing. -/
theorem prefixExcessMonotone {d : ℕ} (hd : 0 < d) (alpha : Fin d → ℝ)
    (hAlpha : Learning.IsDistribution alpha) (hSorted : Antitone alpha)
    (k : ℕ) (hk : 1 ≤ k) (hkd : k ≤ d) : Monotone (prefixExcess alpha k) := by sorry

end QAlgorithms.Papers.Independent.Extend50.P32

end
