-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P32_tailSecondMoment
-- name    : QAlgorithms.Papers.Independent.Extend50.P32.tailSecondMoment
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T09:52:38.420652+00:00
-- url     : https://prove2.me/theorems/5fd1e862-cb42-4084-8f3d-34fe83e4b5b9
-- title:
--   Theorem 4.6: Second moments of a row tail
-- statement:
--   Let $d\ge1$ and let $\alpha=(\alpha_1,\ldots,\alpha_d)$ be a nonincreasing probability vector with nonnegative entries. Draw an iid word of length $n$ with letter law $\alpha$ and let $\lambda$ be its weak-insertion RSK shape, padded to $d$ rows. For $1\le k\le d$, write $\lambda_{\le k}=\sum_{i=1}^k\lambda_i$, $\alpha_{\le k}=\sum_{i=1}^k\alpha_i$, $\alpha_{\ge k}=\sum_{i=k}^d\alpha_i$, and $\alpha_{>k}=\sum_{i=k+1}^d\alpha_i$. Here $n\ge0$; every row parameter lies in $[d]$.
--
--   $$
--   \mathbb E\sum_{i=k}^d\lambda_i^2\le\sum_{i=k}^d(\alpha_in)^2+d\alpha_{\ge k}n.
--   $$
--
--   This controls the empirical Young diagram without an asymptotic spectrum-gap assumption.
-- source:
--   Efficient quantum tomography II, arXiv:1612.00034v1, PDF p. 18, Theorem 4.6

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

/-- Theorem 4.6, PDF p.18: entire row tail, not a single-row second moment.
The k=1 case is credited to OW16 Lemma 3.1. -/
theorem tailSecondMoment {d n : ℕ} (hd : 0 < d) (alpha : Fin d → ℝ)
    (hAlpha : Learning.IsDistribution alpha) (hSorted : Antitone alpha) (k : Fin d) :
    swMean alpha n (fun s => ∑ i : Fin d, if k.val ≤ i.val then row s i.val ^ 2 else 0) ≤
      (∑ i : Fin d, if k.val ≤ i.val then (alpha i * n) ^ 2 else 0) + d * tail alpha k.val * n := by sorry

end QAlgorithms.Papers.Independent.Extend50.P32

end
