-- Prove2me | Theorems.Thm_SubsetSumPartialMatch_SubsetSum_unscreened_cost
-- name    : SubsetSumPartialMatch.SubsetSum.unscreened_cost
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:53:40.409064+00:00
-- url     : https://prove2.me/theorems/a3953c83-ee5c-4302-8c66-88c83b85958b
-- title:
--   Lemma 2.4 — unscreened compatibility cost
-- statement:
--   Let $l,r\ge0$, $\xi>0$ with $l+r\le1/2-2\xi$, and $\varepsilon>0$. Let $6\mid n$, $n>0$, let $s\in\{0,3/n,\dots,1/2\}$ be a layer and $\ell$ the choice of the reduction. Then the conceptual lists $\mathcal A,\mathcal B$ of this layer satisfy
--   $$\mathrm{cost}(|\mathcal A|,|\mathcal B|)\le2^{n/2+(1-\xi)n/3+2\varepsilon n/3+O(1)}.$$
--
--   The $O(1)$ is one absolute constant: it absorbs the rounding of $\ell$ to an even integer. The bound is the cost of running partial match directly on the unfiltered lists.
--
--   Differences from the source:
--   - generalization: the lemma sits inside the proof of Theorem 2.2, in the many-sums case, for an admissible pair $(l,r)$ → the numeric conditions $l,r\ge0$, $\xi>0$, $l+r\le1/2-2\xi$ only, with no assumption on $N_{\mathrm{sum}}$; reason: the lemma uses neither admissibility nor the size of $N_{\mathrm{sum}}$; every admissible pair in that case satisfies these conditions
--   - encoding: $s\in\{0,3/n,\dots,1/2\}$ → $w=sn/3\in\{0,\dots,n/6\}$ with $s=3w/n$; reason: the same finite set of layers
--   - encoding: $O(1)$ → one constant $K$, chosen before all other quantities; reason: it absorbs only the rounding of $\ell$, as the proof says
-- source:
--   Li & Ye, Subset Sum via Partial Match, STOC 2027 submission #24, preprint, source.pdf sha256 e5f396c346fb73c14219a019a35c9a16b1adc4b4b84978d3658736d31958ae5c, p. 12, Lemma 2.4

import Mathlib
import Definitions.Def_SubsetSumPartialMatch_SubsetSum_Reduction

namespace SubsetSumPartialMatch.SubsetSum

/-- Lemma 2.4. In every layer, the cost of partial match on the full conceptual lists is at most
`2^{n/2 + (1-ξ)n/3 + 2εn/3 + O(1)}`, with one absolute constant in the `O(1)`. -/
theorem unscreened_cost :
    ∃ K : ℝ, ∀ l r ξ ε : ℝ, 0 ≤ l → 0 ≤ r → 0 < ξ → l + r ≤ 1 / 2 - 2 * ξ → 0 < ε →
      ∀ n w : ℕ, 6 ∣ n → 0 < n → w ≤ n / 6 →
        pmCost n l r ε (density n w)
            ((leftList n (splitPoint n l r (density n w))).card : ℝ)
            ((rightList n (splitPoint n l r (density n w)) w).card : ℝ) ≤
          (2 : ℝ) ^ ((n : ℝ) / 2 + (1 - ξ) * n / 3 + 2 * ε * n / 3 + K) := by sorry

end SubsetSumPartialMatch.SubsetSum
