-- Prove2me | Theorems.Thm_SubsetSumPartialMatch_SubsetSum_good_layer_exists
-- name    : SubsetSumPartialMatch.SubsetSum.good_layer_exists
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:53:25.066718+00:00
-- url     : https://prove2.me/theorems/a4f5e121-af61-498d-87a4-22cedd832131
-- title:
--   Lemma 2.5 — a support layer has many correct keys
-- statement:
--   Under the standing conditions of the reduction ($l,r\ge0$, $\xi>0$, $l+r\le1/2-2\xi$, $6\mid n$, $n>0$), fix a solution $c$ of the instance $(z,\tau)$. For some $s\in\{0,3/n,\dots,1/2\}$ there are at least
--   $$\frac{N_{\mathrm{sum}}}{n/3+2}$$
--   distinct correct keys.
--
--   Such a value of $s$ is called the good layer. The algorithm does not need to know it, since it tries every layer.
--
--   Differences from the source:
--   - generalization: the lemma sits inside the proof of Theorem 2.2, in the many-sums case, for an admissible pair $(l,r)$ → the numeric conditions $l,r\ge0$, $\xi>0$, $l+r\le1/2-2\xi$ only, with no assumption on $N_{\mathrm{sum}}$; reason: the lemma uses neither admissibility nor the size of $N_{\mathrm{sum}}$; every admissible pair in that case satisfies these conditions
--   - encoding: $s\in\{0,3/n,\dots,1/2\}$ → $w=sn/3\in\{0,\dots,n/6\}$ with $s=3w/n$; reason: the same finite set of layers
-- source:
--   Li & Ye, Subset Sum via Partial Match, STOC 2027 submission #24, preprint, source.pdf sha256 e5f396c346fb73c14219a019a35c9a16b1adc4b4b84978d3658736d31958ae5c, p. 12, Lemma 2.5

import Mathlib
import Definitions.Def_SubsetSumPartialMatch_SubsetSum_Reduction

namespace SubsetSumPartialMatch.SubsetSum

/-- Lemma 2.5. For a fixed solution `c`, some layer has at least `N_sum / (n/3 + 2)` distinct
correct keys. -/
theorem good_layer_exists {l r ξ : ℝ} (hl : 0 ≤ l) (hr : 0 ≤ r) (hξ : 0 < ξ)
    (hlr : l + r ≤ 1 / 2 - 2 * ξ) {n : ℕ} (hn : 6 ∣ n) (hpos : 0 < n)
    (z : Fin n → ℤ) (τ : ℤ) (c : Fin n → Bool) (hc : IsSolution z τ c) :
    ∃ w ≤ n / 6, (Nsum z : ℝ) / ((n : ℝ) / 3 + 2) ≤
      ((correctKeys z c (splitPoint n l r (density n w)) w).card : ℝ) := by sorry

end SubsetSumPartialMatch.SubsetSum
