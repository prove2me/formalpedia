-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P32_truncatedWeightedLoss
-- name    : QAlgorithms.Papers.Independent.Extend50.P32.truncatedWeightedLoss
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T09:34:18.140155+00:00
-- url     : https://prove2.me/theorems/325e578a-1f98-43f1-9751-0cc3345c86a5
-- title:
--   Theorem 1.10: Truncated Hellinger and chi-squared loss
-- statement:
--   Let $d\ge1$ and let $\alpha=(\alpha_1,\ldots,\alpha_d)$ be a nonincreasing probability vector with nonnegative entries. Draw an iid word of length $n$ with letter law $\alpha$ and let $\lambda$ be its weak-insertion RSK shape, padded to $d$ rows. For $1\le k\le d$, write $\lambda_{\le k}=\sum_{i=1}^k\lambda_i$, $\alpha_{\le k}=\sum_{i=1}^k\alpha_i$, $\alpha_{\ge k}=\sum_{i=k}^d\alpha_i$, and $\alpha_{>k}=\sum_{i=k+1}^d\alpha_i$. For $n\ge1$, put $\bar\lambda=\lambda/n$. Hellinger squared is $\sum_i(\sqrt{a_i}-\sqrt{b_i})^2$, chi-squared is $\sum_i(a_i-b_i)^2/b_i$, and KL is $\sum_i a_i\ln(a_i/b_i)$. The estimate is the first argument, zero-over-zero terms contribute zero, and positive estimated mass at zero true mass gives infinite divergence. A superscript $(k)$ retains only the first $k$ terms, without renormalization.
--
--   $$
--   \mathbb E\,D^{(k)}(\bar\lambda,\alpha)\le\frac{46kd}{n},\qquad D^{(k)}\in\{d_{H^2}^{(k)},d_{\chi^2}^{(k)}\}.
--   $$
--
--   This controls the empirical Young diagram without an asymptotic spectrum-gap assumption.
-- source:
--   Efficient quantum tomography II, arXiv:1612.00034v1, PDF p. 4, Theorem 1.10

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

/-- Theorem 1.10, PDF p.4: the two loss functions are already truncated. -/
theorem truncatedWeightedLoss {d n : ℕ} (hd : 0 < d) (hn : 0 < n) (alpha : Fin d → ℝ)
    (hAlpha : Learning.IsDistribution alpha) (hSorted : Antitone alpha)
    (k : ℕ) (hk : 1 ≤ k) (hkd : k ≤ d) (metric : WeightedMetric) :
    swMeanExt alpha n (fun s => weightedLoss metric k (normalizedShapeRows n s) alpha) ≤
      ENNReal.ofReal (46 * (k : ℝ) * d / n) := by sorry

end QAlgorithms.Papers.Independent.Extend50.P32

end
