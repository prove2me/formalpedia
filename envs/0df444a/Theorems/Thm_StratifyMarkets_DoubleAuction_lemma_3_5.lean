-- Prove2me | Theorems.Thm_StratifyMarkets_DoubleAuction_lemma_3_5
-- name    : StratifyMarkets.DoubleAuction.lemma_3_5
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T00:54:35.277659+00:00
-- url     : https://prove2.me/theorems/c196c36a-4947-46e4-a867-1a97f11d6b92
-- title:
--   Lemma 3.5 — ordered fully tradable matchings with OrderedMatching ≥ SellerProfit/4 and with OrderedMatching ≥ BuyerProfit/4
-- statement:
--   For every bilateral trade instance $(F,G)$ there is an ordered fully tradable matching with
--   $$\mathrm{OrderedMatching}\ge\frac14\,\mathrm{SellerProfit},$$
--   and there is an ordered fully tradable matching with $\mathrm{OrderedMatching}\ge\frac14\,\mathrm{BuyerProfit}$. Here SellerProfit and BuyerProfit are the expected profits of the seller-pricing and buyer-pricing mechanisms at profit-maximizing prices in $[0,1]$. It is Step 2 of the bilateral argument.
--
--   Differences from the source:
--   - encoding: F and G are continuous distributions supported on [0, 1], v and c independent → a `BTInstance`: probability measures μB, μS with no atoms (`NullSingletonClass`) and mass 1 on [0, 1]; expectations over the product `μS.prod μB`; reason: a CDF is continuous exactly when its law has no atoms; same instances
--   - encoding: SellerProfit(c) = (s_c − c) F̄(s_c) and BuyerProfit(v) = (v − b_v) G(b_v) at profit-maximizing prices → the suprema over s ∈ [0, 1] of (s − c) F̄(s) and over b ∈ [0, 1] of (v − b) G(b); reason: the maxima are attained (continuous functions on [0, 1]), so the values agree and no argmax selection is needed
--   - encoding: indices k = 1, …, N → 0-based `k : Fin N`, submarket k is [m k.castSucc, m k.succ] with price p k; reason: relabelling only
-- source:
--   Deng, Lin, Schoepflin, Wang, Stratifying Markets for Efficient Trade, STOC 2027 submission (manuscript sha256 49372bcf…), p. 20, Lemma 3.5

import Mathlib
import Definitions.Def_StratifyMarkets_DoubleAuction_Bilateral
import Definitions.Def_StratifyMarkets_DoubleAuction_Stratification

open MeasureTheory

namespace StratifyMarkets.DoubleAuction

/-- Lemma 3.5 (p. 20): for every bilateral trade instance there is an ordered fully tradable
matching with `OrderedMatching ≥ SellerProfit / 4`, and there is one with
`OrderedMatching ≥ BuyerProfit / 4`. -/
theorem lemma_3_5 (I : BTInstance) :
    (∃ M : OrderedMatching, 1 / 4 * I.sellerProfit ≤ I.orderedMatching M) ∧
    (∃ M : OrderedMatching, 1 / 4 * I.buyerProfit ≤ I.orderedMatching M) := by sorry

end StratifyMarkets.DoubleAuction
