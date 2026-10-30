-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P32_classicalLossComparisons
-- name    : QAlgorithms.Papers.Independent.Extend50.P32.classicalLossComparisons
-- status  : Proved
-- author  : @Gohan
-- created : 2026-10-29T09:44:14.767866+00:00
-- url     : https://prove2.me/theorems/172e33b0-7825-4e84-a44e-7c79c06021a5
-- title:
--   Proposition 2.7: Classical loss comparisons
-- statement:
--   Let $d\ge1$ and let $a,b$ be nonnegative probability vectors on $[d]$, and let $1\le k\le d$. For $n\ge1$, put $\bar\lambda=\lambda/n$. Hellinger squared is $\sum_i(\sqrt{a_i}-\sqrt{b_i})^2$, chi-squared is $\sum_i(a_i-b_i)^2/b_i$, and KL is $\sum_i a_i\ln(a_i/b_i)$. The estimate is the first argument, zero-over-zero terms contribute zero, and positive estimated mass at zero true mass gives infinite divergence. A superscript $(k)$ retains only the first $k$ terms, without renormalization.
--
--   $$
--   d_{H^2}(a,b)\le d_{\chi^2}(a,b),\qquad d_{H^2}^{(k)}(a,b)\le d_{\chi^2}^{(k)}(a,b),\qquad d_{\mathrm{KL}}(a,b)\le d_{\chi^2}(a,b).
--   $$
--
--   This isolates the source comparison or construction with all of its domain and occurrence conventions retained.
-- source:
--   Efficient quantum tomography II, arXiv:1612.00034v1, PDF p. 12, Proposition 2.7

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

/-- Proposition 2.7, PDF p.12: full/full, truncated/truncated, and full KL/chi.
No probability support is excluded. -/
theorem classicalLossComparisons {d : ℕ} (hd : 0 < d) (alpha beta : Fin d → ℝ)
    (hAlpha : Learning.IsDistribution alpha) (hBeta : Learning.IsDistribution beta)
    (k : ℕ) (hk : 1 ≤ k) (hkd : k ≤ d) :
    ENNReal.ofReal (h2 d alpha beta) ≤ chi2 d alpha beta ∧
    ENNReal.ofReal (h2 k alpha beta) ≤ chi2 k alpha beta ∧
    kl alpha beta ≤ chi2 d alpha beta := by sorry

end QAlgorithms.Papers.Independent.Extend50.P32

end
