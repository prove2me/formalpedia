-- Prove2me | Theorems.Thm_StratifyMarkets_DoubleAuction_lemma_4_5
-- name    : StratifyMarkets.DoubleAuction.lemma_4_5
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T00:56:02.586401+00:00
-- url     : https://prove2.me/theorems/7d3952f8-aac1-458b-b1eb-330c75302453
-- title:
--   Lemma 4.5 — for λ ≥ 4, WorstRationed(p_mid) ≥ (λ/32)(p̄ − p̲) at p_mid = (p̄ + p̲)/2
-- statement:
--   Let a double auction instance have $\lambda\ge4$ (4.1), and let $\bar p$, $\underline p$ be excess-supply and excess-demand prices (4.2). With the midpoint $p_{\mathrm{mid}}=(\bar p+\underline p)/2$,
--   $$\mathrm{WorstRationed}(p_{\mathrm{mid}})\ge\frac{\lambda}{32}\,(\bar p-\underline p).$$
--   This bounds the gap term of Lemma 4.3.
--
--   Differences from the source:
--   - encoding: continuous F_1..F_n, G_1..G_m supported on [0, 1], all values and costs mutually independent → a `DAInstance n m`: no-atom probability measures with mass 1 on [0, 1]; expectations over the product `(Measure.pi μB).prod (Measure.pi μS)`; reason: same instances; independence is the product measure
--   - encoding: λ defined in (4.1) from the balanced price p̃ → a balanced price `pt` (`IsBalancedPrice`: pt ∈ [0, 1], E_v[B_pt] = E_c[S_pt]) as a variable, with λ = `expB pt`; reason: p̃ need not be unique but λ is the same for every balanced price, and a balanced price exists by continuity; quantifying over every one is at least as strong as fixing one
--   - encoding: the excess-supply price p̄ and the excess-demand price p̲ of (4.2) → arbitrary `pbar`, `plow` ∈ [0, 1] satisfying (4.2) (`IsExcessSupplyPrice`, `IsExcessDemandPrice`); reason: (4.2) need not have a unique solution; every solution lies in [0, 1] when λ ≥ 4, and quantifying over all of them is at least as strong as fixing one
-- source:
--   Deng, Lin, Schoepflin, Wang, Stratifying Markets for Efficient Trade, STOC 2027 submission (manuscript sha256 49372bcf…), p. 31, Lemma 4.5

import Mathlib
import Definitions.Def_StratifyMarkets_DoubleAuction_Instance
import Definitions.Def_StratifyMarkets_DoubleAuction_WorstRationed
import Definitions.Def_StratifyMarkets_DoubleAuction_Prices

open MeasureTheory

namespace StratifyMarkets.DoubleAuction

/-- Lemma 4.5 (p. 31): if `λ ≥ 4`, then `WorstRationed(p_mid) ≥ (λ/32)(p̄ − p̲)` with
`p_mid = (p̄ + p̲)/2`, for every excess-supply price `p̄` and excess-demand price `p̲`. -/
theorem lemma_4_5 {n m : ℕ} (I : DAInstance n m) (pt pbar plow : ℝ)
    (hpt : I.IsBalancedPrice pt) (hlam : 4 ≤ I.expB pt)
    (hpbar : I.IsExcessSupplyPrice pbar) (hplow : I.IsExcessDemandPrice plow) :
    I.expB pt / 32 * (pbar - plow) ≤ I.worstRationed ((pbar + plow) / 2) := by sorry

end StratifyMarkets.DoubleAuction
