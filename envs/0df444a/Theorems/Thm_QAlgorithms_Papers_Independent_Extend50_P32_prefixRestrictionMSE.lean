-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P32_prefixRestrictionMSE
-- name    : QAlgorithms.Papers.Independent.Extend50.P32.prefixRestrictionMSE
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T09:54:51.171983+00:00
-- url     : https://prove2.me/theorems/7d915dfc-0b3c-4275-9064-03fe7a7afc64
-- title:
--   Lemma 4.9: Prefix restriction MSE reduction
-- statement:
--   Let $d\ge1$ and let $\alpha=(\alpha_1,\ldots,\alpha_d)$ be a nonincreasing probability vector with nonnegative entries. Draw an iid word of length $n$ with letter law $\alpha$ and let $\lambda$ be its weak-insertion RSK shape, padded to $d$ rows. For $1\le k\le d$, write $\lambda_{\le k}=\sum_{i=1}^k\lambda_i$, $\alpha_{\le k}=\sum_{i=1}^k\alpha_i$, $\alpha_{\ge k}=\sum_{i=k}^d\alpha_i$, and $\alpha_{>k}=\sum_{i=k+1}^d\alpha_i$. Here $n\ge0$; every row parameter lies in $[d]$. From the same iid word retain letters at most $k$, obtaining length $m$ and shape $\lambda^{(\cdots k)}$. The conditional letter masses are $\alpha_i/\alpha_{\le k}$, whose denominator is positive; this constructs the variables on the right.
--
--   $$
--   \mathbb E(\lambda_i-\alpha_i n)^2\le2\mathbb E\left(\lambda_i^{(\cdots k)}-\frac{\alpha_i}{\alpha_{\le k}}m\right)^2+44\alpha_{\ge i}n,\qquad1\le i\le k\le d.
--   $$
--
--   This controls the empirical Young diagram without an asymptotic spectrum-gap assumption.
-- source:
--   Efficient quantum tomography II, arXiv:1612.00034v1, PDF p. 19, Lemma 4.9

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

/-- Lemma 4.9, PDF pp.19-20: m and restricted shape are CONSTRUCTED by
retaining the first k letters of the same word. Prefix mass is positive
from sortedness and k>=1; no extra full-support assumption. -/
theorem prefixRestrictionMSE {d n : ℕ} (hd : 0 < d) (alpha : Fin d → ℝ)
    (hAlpha : Learning.IsDistribution alpha) (hSorted : Antitone alpha)
    (i k : Fin d) (hik : i ≤ k) :
    rowMSE alpha n i ≤ 2 * wordMean alpha n (fun w =>
      let v := prefixWord w (k.val + 1)
      (row (shape v) i.val - (alpha i / prefixMass alpha (k.val + 1)) * v.length) ^ 2) +
      44 * tail alpha i.val * n := by sorry

end QAlgorithms.Papers.Independent.Extend50.P32

end
