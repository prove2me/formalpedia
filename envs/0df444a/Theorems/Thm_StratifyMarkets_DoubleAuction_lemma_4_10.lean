-- Prove2me | Theorems.Thm_StratifyMarkets_DoubleAuction_lemma_4_10
-- name    : StratifyMarkets.DoubleAuction.lemma_4_10
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T00:56:22.787137+00:00
-- url     : https://prove2.me/theorems/60b025eb-5a02-460b-a1ec-952a16b4a0df
-- title:
--   Lemma 4.10 — for λ < 4, WorstRationed(p̃) ≥ (1/7) E[RealizedFB · 1{τ > 5}] at the balanced price
-- statement:
--   For every double auction instance with $\lambda<4$, where $\lambda$ is defined in (4.1), the worst-rationed rule with the balanced price $\tilde p$ satisfies
--   $$\mathrm{WorstRationed}(\tilde p)\ge\frac17\,\mathbb E_{\mathbf v,\mathbf c}\big[\mathrm{RealizedFB}\cdot\mathbb 1\{\tau>5\}\big].$$
--   Here $\tau$ is the number of efficient trades and RealizedFB the realized first-best gains (§2.2).
--
--   Differences from the source:
--   - encoding: continuous F_1..F_n, G_1..G_m supported on [0, 1], all values and costs mutually independent → a `DAInstance n m`: no-atom probability measures with mass 1 on [0, 1]; expectations over the product `(Measure.pi μB).prod (Measure.pi μS)`; reason: same instances; independence is the product measure
--   - encoding: λ defined in (4.1) from the balanced price p̃ → a balanced price `pt` (`IsBalancedPrice`: pt ∈ [0, 1], E_v[B_pt] = E_c[S_pt]) as a variable, with λ = `expB pt`; reason: p̃ need not be unique but λ is the same for every balanced price, and a balanced price exists by continuity; quantifying over every one is at least as strong as fixing one
-- source:
--   Deng, Lin, Schoepflin, Wang, Stratifying Markets for Efficient Trade, STOC 2027 submission (manuscript sha256 49372bcf…), p. 33, Lemma 4.10

import Mathlib
import Definitions.Def_StratifyMarkets_DoubleAuction_Instance
import Definitions.Def_StratifyMarkets_DoubleAuction_WorstRationed
import Definitions.Def_StratifyMarkets_DoubleAuction_Prices

open MeasureTheory

namespace StratifyMarkets.DoubleAuction

/-- Lemma 4.10 (p. 33): if `λ < 4`, the worst-rationed rule at (every) balanced price `p̃` has
`WorstRationed(p̃) ≥ (1/7) E_{𝐯,𝐜}[RealizedFB · 1{τ > 5}]`. -/
theorem lemma_4_10 {n m : ℕ} (I : DAInstance n m) (pt : ℝ)
    (hpt : I.IsBalancedPrice pt) (hlam : I.expB pt < 4) :
    1 / 7 * I.FBtauGt5 ≤ I.worstRationed pt := by sorry

end StratifyMarkets.DoubleAuction
