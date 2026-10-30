-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P32_modifiedMultinomialPrefix
-- name    : QAlgorithms.Papers.Independent.Extend50.P32.modifiedMultinomialPrefix
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T09:46:22.819312+00:00
-- url     : https://prove2.me/theorems/ae8ba9a3-1e16-4feb-8d9a-9ad227114828
-- title:
--   Proposition 3.6: Modified multinomial expected prefix excess
-- statement:
--   Let $d\ge1$ and let $\alpha=(\alpha_1,\ldots,\alpha_d)$ be a nonincreasing probability vector with nonnegative entries. Draw an iid word of length $n$ with letter law $\alpha$ and let $\lambda$ be its weak-insertion RSK shape, padded to $d$ rows. For $1\le k\le d$, write $\lambda_{\le k}=\sum_{i=1}^k\lambda_i$, $\alpha_{\le k}=\sum_{i=1}^k\alpha_i$, $\alpha_{\ge k}=\sum_{i=k}^d\alpha_i$, and $\alpha_{>k}=\sum_{i=k+1}^d\alpha_i$. Assume $n\ge1$ and all $\alpha_i$ are distinct. For an ordinary multinomial histogram $h$, the modified multinomial signed weight multiplies its probability by $1+\sum_{i<j}(\alpha_j h_i/\alpha_i-h_j)/(n(\alpha_i-\alpha_j))$. This cancelled expression permits a zero last mass; these signed weights are not probabilities. The excess is $\operatorname{Excess}_k(\alpha)=\sum_{i\le k<j}\alpha_j/(\alpha_i-\alpha_j)$.
--
--   $$
--   \mathbb E_{h\sim\operatorname{ModMult}(n,\alpha)}\bigl[h_{\le k}-n\alpha_{\le k}\bigr]=\operatorname{Excess}_k(\alpha).
--   $$
--
--   This quantifies the excess of the leading rows above their linear multinomial scale.
-- source:
--   Efficient quantum tomography II, arXiv:1612.00034v1, PDF p. 14, Proposition 3.6

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

/-- Proposition 3.6, PDF pp.14-15. Printed: a constant E_k^(n)(alpha) inside
the expectation. Corrected: centered histogram PREFIX statistic, as the
rowwise proof and telescoping require. n>0 is the domain of phi's 1/n;
alpha_d=0 is retained by cancellation. Independent moderation required. -/
theorem modifiedMultinomialPrefix {d n : ℕ} (hd : 0 < d) (hn : 0 < n)
    (alpha : Fin d → ℝ) (hAlpha : Learning.IsDistribution alpha)
    (hSorted : Antitone alpha) (hDistinct : Function.Injective alpha)
    (k : ℕ) (hk : 1 ≤ k) (hkd : k ≤ d) :
    modifiedMean alpha n (fun h => prefixMass h k - prefixMass alpha k * n) = (spectralPrefixExcessLimit alpha k).toReal := by sorry

end QAlgorithms.Papers.Independent.Extend50.P32

end
