-- Prove2me | Theorems.Thm_StratifyMarkets_DoubleAuction_lemma_3_6
-- name    : StratifyMarkets.DoubleAuction.lemma_3_6
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T00:54:35.94707+00:00
-- url     : https://prove2.me/theorems/b6e989b9-37ce-4ab3-ad25-334a3818b7d7
-- title:
--   Lemma 3.6 — an ordered fully tradable matching with OrderedMatching ≥ ROProfit/4
-- statement:
--   For every bilateral trade instance $(F,G)$ there is an ordered fully tradable matching with
--   $$\mathrm{OrderedMatching}\ge\frac14\,\mathrm{ROProfit},$$
--   where $\mathrm{ROProfit}=\tfrac12\mathrm{BuyerProfit}+\tfrac12\mathrm{SellerProfit}$. It combines the two matchings of Lemma 3.5.
--
--   Differences from the source:
--   - encoding: F and G are continuous distributions supported on [0, 1], v and c independent → a `BTInstance`: probability measures μB, μS with no atoms (`NullSingletonClass`) and mass 1 on [0, 1]; expectations over the product `μS.prod μB`; reason: a CDF is continuous exactly when its law has no atoms; same instances
--   - encoding: SellerProfit(c) = (s_c − c) F̄(s_c) and BuyerProfit(v) = (v − b_v) G(b_v) at profit-maximizing prices → the suprema over s ∈ [0, 1] of (s − c) F̄(s) and over b ∈ [0, 1] of (v − b) G(b); reason: the maxima are attained (continuous functions on [0, 1]), so the values agree and no argmax selection is needed
--   - encoding: indices k = 1, …, N → 0-based `k : Fin N`, submarket k is [m k.castSucc, m k.succ] with price p k; reason: relabelling only
-- source:
--   Deng, Lin, Schoepflin, Wang, Stratifying Markets for Efficient Trade, STOC 2027 submission (manuscript sha256 49372bcf…), p. 22, Lemma 3.6

import Mathlib
import Definitions.Def_StratifyMarkets_DoubleAuction_Bilateral
import Definitions.Def_StratifyMarkets_DoubleAuction_Stratification

open MeasureTheory

namespace StratifyMarkets.DoubleAuction

/-- Lemma 3.6 (p. 22): for every bilateral trade instance there is an ordered fully tradable
matching with `OrderedMatching ≥ ROProfit / 4`. -/
theorem lemma_3_6 (I : BTInstance) :
    ∃ M : OrderedMatching, 1 / 4 * I.roProfit ≤ I.orderedMatching M := by sorry

end StratifyMarkets.DoubleAuction
