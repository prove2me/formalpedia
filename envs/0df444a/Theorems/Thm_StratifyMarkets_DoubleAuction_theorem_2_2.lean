-- Prove2me | Theorems.Thm_StratifyMarkets_DoubleAuction_theorem_2_2
-- name    : StratifyMarkets.DoubleAuction.theorem_2_2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T00:53:24.335051+00:00
-- url     : https://prove2.me/theorems/cd480aa8-e924-453d-8c07-0ff77b11ca87
-- title:
--   Theorem 2.2 [BWZ26] — random-offerer guarantee: FB ≤ e · ROProfit for every bilateral trade instance
-- statement:
--   Let $(F,G)$ be a bilateral trade instance: the buyer's value $v\sim F$ and the seller's cost $c\sim G$ are independent, and $F,G$ are continuous distributions supported on $[0,1]$. Let $\mathrm{FB}=\mathbb E[(v-c)_+]$ be the first-best gains from trade and $\mathrm{ROProfit}=\tfrac12\mathrm{BuyerProfit}+\tfrac12\mathrm{SellerProfit}$ the random offerer's expected profit at profit-maximizing take-it-or-leave-it prices in $[0,1]$. Then
--   $$\mathrm{FB}\le e\cdot\mathrm{ROProfit}.$$
--   This is a cited result of Bei, Wu and Zhou [BWZ26]; the paper does not prove it. It is Step 3 of the proof of Theorem 3.1.
--
--   Differences from the source:
--   - encoding: F and G are continuous distributions supported on [0, 1], v and c independent → a `BTInstance`: probability measures μB, μS with no atoms (`NullSingletonClass`) and mass 1 on [0, 1]; expectations over the product `μS.prod μB`; reason: a CDF is continuous exactly when its law has no atoms; same instances
--   - encoding: SellerProfit(c) = (s_c − c) F̄(s_c) and BuyerProfit(v) = (v − b_v) G(b_v) at profit-maximizing prices → the suprema over s ∈ [0, 1] of (s − c) F̄(s) and over b ∈ [0, 1] of (v − b) G(b); reason: the maxima are attained (continuous functions on [0, 1]), so the values agree and no argmax selection is needed
-- source:
--   Deng, Lin, Schoepflin, Wang, Stratifying Markets for Efficient Trade, STOC 2027 submission (manuscript sha256 49372bcf…), p. 8, Theorem 2.2 (cited: [BWZ26])

import Mathlib
import Definitions.Def_StratifyMarkets_DoubleAuction_Bilateral

open MeasureTheory

namespace StratifyMarkets.DoubleAuction

/-- Theorem 2.2 [BWZ26] (p. 8): for every bilateral trade instance, `FB ≤ e · ROProfit`. -/
theorem theorem_2_2 (I : BTInstance) : I.FB ≤ Real.exp 1 * I.roProfit := by sorry

end StratifyMarkets.DoubleAuction
