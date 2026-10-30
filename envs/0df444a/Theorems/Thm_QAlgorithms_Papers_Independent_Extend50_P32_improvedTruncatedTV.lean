-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P32_improvedTruncatedTV
-- name    : QAlgorithms.Papers.Independent.Extend50.P32.improvedTruncatedTV
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T10:07:48.953234+00:00
-- url     : https://prove2.me/theorems/33bbd394-7762-4d49-a3b3-9b5528906b68
-- title:
--   Unnumbered: Improved truncated-TV coefficient
-- statement:
--   Let $d\ge1$ and let $\alpha=(\alpha_1,\ldots,\alpha_d)$ be a nonincreasing probability vector with nonnegative entries. Draw an iid word of length $n$ with letter law $\alpha$ and let $\lambda$ be its weak-insertion RSK shape, padded to $d$ rows. For $1\le k\le d$, write $\lambda_{\le k}=\sum_{i=1}^k\lambda_i$, $\alpha_{\le k}=\sum_{i=1}^k\alpha_i$, $\alpha_{\ge k}=\sum_{i=k}^d\alpha_i$, and $\alpha_{>k}=\sum_{i=k+1}^d\alpha_i$. For $n\ge1$, put $\bar\lambda=\lambda/n$. Hellinger squared is $\sum_i(\sqrt{a_i}-\sqrt{b_i})^2$, chi-squared is $\sum_i(a_i-b_i)^2/b_i$, and KL is $\sum_i a_i\ln(a_i/b_i)$. The estimate is the first argument, zero-over-zero terms contribute zero, and positive estimated mass at zero true mass gives infinite divergence. A superscript $(k)$ retains only the first $k$ terms, without renormalization.
--
--   $$
--   \mathbb E\,d_{\mathrm{TV}}^{(k)}(\bar\lambda,\alpha)\le\frac{1.5k+0.5}{\sqrt n},\qquad d_{\mathrm{TV}}^{(k)}(a,b)=\frac12\sum_{i=1}^k|a_i-b_i|.
--   $$
--
--   This controls the empirical Young diagram without an asymptotic spectrum-gap assumption.
-- source:
--   Efficient quantum tomography II, arXiv:1612.00034v1, PDF p. 4, Unnumbered

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

/-- Unnumbered improvement after Theorem 1.8, PDF p.4. The plan's missing
truncated-TV convention is supplied by the checked OW16 original,
arXiv:1508.01907v2 PDF p.3, Theorem 1.7. -/
theorem improvedTruncatedTV {d n : ℕ} (hd : 0 < d) (hn : 0 < n) (alpha : Fin d → ℝ)
    (hAlpha : Learning.IsDistribution alpha) (hSorted : Antitone alpha)
    (k : ℕ) (hk : 1 ≤ k) (hkd : k ≤ d) :
    swMean alpha n (fun s => truncatedTV k (normalizedShapeRows n s) alpha) ≤
      ((3 / 2 : ℝ) * k + 1 / 2) / Real.sqrt n := by sorry

end QAlgorithms.Papers.Independent.Extend50.P32

end
