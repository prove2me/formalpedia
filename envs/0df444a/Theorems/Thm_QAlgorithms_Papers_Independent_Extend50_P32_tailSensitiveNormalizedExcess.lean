-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P32_tailSensitiveNormalizedExcess
-- name    : QAlgorithms.Papers.Independent.Extend50.P32.tailSensitiveNormalizedExcess
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T09:58:46.836491+00:00
-- url     : https://prove2.me/theorems/dbaa49f4-83e1-4614-8660-a08ece6a4b56
-- title:
--   Proposition 4.14: Tail-sensitive normalized prefix excess
-- statement:
--   Let $d\ge1$ and let $\alpha=(\alpha_1,\ldots,\alpha_d)$ be a nonincreasing probability vector with nonnegative entries. Draw an iid word of length $n$ with letter law $\alpha$ and let $\lambda$ be its weak-insertion RSK shape, padded to $d$ rows. For $1\le k\le d$, write $\lambda_{\le k}=\sum_{i=1}^k\lambda_i$, $\alpha_{\le k}=\sum_{i=1}^k\alpha_i$, $\alpha_{\ge k}=\sum_{i=k}^d\alpha_i$, and $\alpha_{>k}=\sum_{i=k+1}^d\alpha_i$. For $n\ge1$, put $\bar\lambda=\lambda/n$. Hellinger squared is $\sum_i(\sqrt{a_i}-\sqrt{b_i})^2$, chi-squared is $\sum_i(a_i-b_i)^2/b_i$, and KL is $\sum_i a_i\ln(a_i/b_i)$. The estimate is the first argument, zero-over-zero terms contribute zero, and positive estimated mass at zero true mass gives infinite divergence. A superscript $(k)$ retains only the first $k$ terms, without renormalization. The constant $C>0$ is absolute and precedes all dimensions, sample counts, spectra and states.
--
--   $$
--   \exists C>0:\quad\mathbb E[\bar\lambda_{\le k}-\alpha_{\le k}]\le Ck\sqrt{\frac{\alpha_{>k}}n}.
--   $$
--
--   This controls the empirical Young diagram without an asymptotic spectrum-gap assumption.
-- source:
--   Efficient quantum tomography II, arXiv:1612.00034v1, PDF p. 22, Proposition 4.14

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

/-- Proposition 4.14, PDF p.22: k is outside the square root; zero tail allowed. -/
theorem tailSensitiveNormalizedExcess : ∃ C : ℝ, 0 < C ∧
    ∀ (d n : ℕ), 0 < d → 0 < n → ∀ alpha : Fin d → ℝ,
      Learning.IsDistribution alpha → Antitone alpha → ∀ k : ℕ, 1 ≤ k → k ≤ d →
        normalizedExcess alpha k n ≤ C * k * Real.sqrt (tail alpha k) / Real.sqrt n := by sorry

end QAlgorithms.Papers.Independent.Extend50.P32

end
