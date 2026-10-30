-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P32_tailSensitiveExpectedRows
-- name    : QAlgorithms.Papers.Independent.Extend50.P32.tailSensitiveExpectedRows
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T09:51:38.606949+00:00
-- url     : https://prove2.me/theorems/be80b061-270f-473c-8ce5-8a1fdc03e840
-- title:
--   Theorem 4.5: Tail-sensitive expected row bounds
-- statement:
--   Let $d\ge1$ and let $\alpha=(\alpha_1,\ldots,\alpha_d)$ be a nonincreasing probability vector with nonnegative entries. Draw an iid word of length $n$ with letter law $\alpha$ and let $\lambda$ be its weak-insertion RSK shape, padded to $d$ rows. For $1\le k\le d$, write $\lambda_{\le k}=\sum_{i=1}^k\lambda_i$, $\alpha_{\le k}=\sum_{i=1}^k\alpha_i$, $\alpha_{\ge k}=\sum_{i=k}^d\alpha_i$, and $\alpha_{>k}=\sum_{i=k+1}^d\alpha_i$. Here $n\ge0$; every row parameter lies in $[d]$.
--
--   $$
--   \alpha_kn-2\sqrt{\alpha_kkn}\le\mathbb E\lambda_k\le\alpha_kn+2\sqrt{\alpha_{\ge k}n}.
--   $$
--
--   This controls the empirical Young diagram without an asymptotic spectrum-gap assumption.
-- source:
--   Efficient quantum tomography II, arXiv:1612.00034v1, PDF p. 17, Theorem 4.5

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

/-- Theorem 4.5, PDF pp.17-18: tail mass in the upper radicand and source
one-based k in the lower radicand. -/
theorem tailSensitiveExpectedRows {d n : ℕ} (hd : 0 < d) (alpha : Fin d → ℝ)
    (hAlpha : Learning.IsDistribution alpha) (hSorted : Antitone alpha) (k : Fin d) :
    alpha k * n - 2 * Real.sqrt (alpha k * (k.val + 1) * n) ≤ swMean alpha n (fun s => row s k.val) ∧
    swMean alpha n (fun s => row s k.val) ≤ alpha k * n + 2 * Real.sqrt (tail alpha k.val * n) := by sorry

end QAlgorithms.Papers.Independent.Extend50.P32

end
