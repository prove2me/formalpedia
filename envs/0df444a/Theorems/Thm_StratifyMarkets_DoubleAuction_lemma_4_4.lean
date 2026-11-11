-- Prove2me | Theorems.Thm_StratifyMarkets_DoubleAuction_lemma_4_4
-- name    : StratifyMarkets.DoubleAuction.lemma_4_4
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T00:55:40.365253+00:00
-- url     : https://prove2.me/theorems/d9424d43-5203-4a04-a10f-42d17ad09bf0
-- title:
--   Lemma 4.4 — for λ ≥ 4, WorstRationed(p̄) ≥ ¼ Σ_i E[(v_i − p̄)_+] and WorstRationed(p̲) ≥ ¼ Σ_j E[(p̲ − c_j)_+]
-- statement:
--   Let a double auction instance have $\lambda\ge4$ (4.1), and let $\bar p$, $\underline p$ be excess-supply and excess-demand prices (4.2). The worst-rationed rule at these global prices satisfies
--   $$\mathrm{WorstRationed}(\bar p)\ge\frac14\sum_{i=1}^n\mathbb E_{\mathbf v}\big[(v_i-\bar p)_+\big]\quad\text{and}\quad\mathrm{WorstRationed}(\underline p)\ge\frac14\sum_{j=1}^m\mathbb E_{\mathbf c}\big[(\underline p-c_j)_+\big].$$
--   These bound the first two terms of Lemma 4.3.
--
--   Differences from the source:
--   - encoding: continuous F_1..F_n, G_1..G_m supported on [0, 1], all values and costs mutually independent → a `DAInstance n m`: no-atom probability measures with mass 1 on [0, 1]; expectations over the product `(Measure.pi μB).prod (Measure.pi μS)`; reason: same instances; independence is the product measure
--   - encoding: λ defined in (4.1) from the balanced price p̃ → a balanced price `pt` (`IsBalancedPrice`: pt ∈ [0, 1], E_v[B_pt] = E_c[S_pt]) as a variable, with λ = `expB pt`; reason: p̃ need not be unique but λ is the same for every balanced price, and a balanced price exists by continuity; quantifying over every one is at least as strong as fixing one
--   - encoding: the excess-supply price p̄ and the excess-demand price p̲ of (4.2) → arbitrary `pbar`, `plow` ∈ [0, 1] satisfying (4.2) (`IsExcessSupplyPrice`, `IsExcessDemandPrice`); reason: (4.2) need not have a unique solution; every solution lies in [0, 1] when λ ≥ 4, and quantifying over all of them is at least as strong as fixing one
-- source:
--   Deng, Lin, Schoepflin, Wang, Stratifying Markets for Efficient Trade, STOC 2027 submission (manuscript sha256 49372bcf…), p. 29, Lemma 4.4 (proof pp. 30–31)

import Mathlib
import Definitions.Def_StratifyMarkets_DoubleAuction_Instance
import Definitions.Def_StratifyMarkets_DoubleAuction_WorstRationed
import Definitions.Def_StratifyMarkets_DoubleAuction_Prices

open MeasureTheory

namespace StratifyMarkets.DoubleAuction

/-- Lemma 4.4 (p. 29): if `λ ≥ 4`, then `WorstRationed(p̄) ≥ (1/4) Σ_i E_𝐯[(v_i − p̄)_+]` and
`WorstRationed(p̲) ≥ (1/4) Σ_j E_𝐜[(p̲ − c_j)_+]`, for every excess-supply price `p̄` and
excess-demand price `p̲`. -/
theorem lemma_4_4 {n m : ℕ} (I : DAInstance n m) (pt pbar plow : ℝ)
    (hpt : I.IsBalancedPrice pt) (hlam : 4 ≤ I.expB pt)
    (hpbar : I.IsExcessSupplyPrice pbar) (hplow : I.IsExcessDemandPrice plow) :
    1 / 4 * I.buyerSurplus pbar ≤ I.worstRationed pbar ∧
    1 / 4 * I.sellerSurplus plow ≤ I.worstRationed plow := by sorry

end StratifyMarkets.DoubleAuction
