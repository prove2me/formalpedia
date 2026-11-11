-- Prove2me | Theorems.Thm_StratifyMarkets_DoubleAuction_lemma_3_2
-- name    : StratifyMarkets.DoubleAuction.lemma_3_2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T00:54:21.351103+00:00
-- url     : https://prove2.me/theorems/918b0757-cde9-4d78-8e56-98690179049a
-- title:
--   Lemma 3.2 — every ordered fully tradable matching converts into a stratification with at least one-third of its gains from trade
-- statement:
--   Let $(F,G)$ be a bilateral trade instance and let $(\mathcal B,\mathcal S)$ be an ordered fully tradable matching (Definition 2.6), with gains $\mathrm{OrderedMatching}$. Then there is a market stratification (Definition 2.3) whose bilateral gains from trade satisfy
--   $$\mathrm{Strat}\ge\frac13\,\mathrm{OrderedMatching}.$$
--   This is Step 1 of the bilateral argument (Figure 3.1).
--
--   Differences from the source:
--   - encoding: F and G are continuous distributions supported on [0, 1], v and c independent → a `BTInstance`: probability measures μB, μS with no atoms (`NullSingletonClass`) and mass 1 on [0, 1]; expectations over the product `μS.prod μB`; reason: a CDF is continuous exactly when its law has no atoms; same instances
--   - encoding: indices k = 1, …, N → 0-based `k : Fin N`, submarket k is [m k.castSucc, m k.succ] with price p k; reason: relabelling only
--   - encoding: the matching 'can be converted into a stratification that achieves at least one-third of its gains from trade' → ∃ σ : Stratification, OrderedMatching(M)/3 ≤ Strat(σ), for the same instance; reason: the conversion is the existence of such a stratification
-- source:
--   Deng, Lin, Schoepflin, Wang, Stratifying Markets for Efficient Trade, STOC 2027 submission (manuscript sha256 49372bcf…), p. 16, Lemma 3.2

import Mathlib
import Definitions.Def_StratifyMarkets_DoubleAuction_Bilateral
import Definitions.Def_StratifyMarkets_DoubleAuction_Stratification

open MeasureTheory

namespace StratifyMarkets.DoubleAuction

/-- Lemma 3.2 (p. 16): every ordered fully tradable matching can be converted into a stratification
that achieves at least one-third of its gains from trade. -/
theorem lemma_3_2 (I : BTInstance) (M : OrderedMatching) :
    ∃ σ : Stratification, I.orderedMatching M / 3 ≤ I.strat σ := by sorry

end StratifyMarkets.DoubleAuction
