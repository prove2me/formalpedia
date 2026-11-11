-- Prove2me | Theorems.Thm_StratifyMarkets_DoubleAuction_lemma_4_6
-- name    : StratifyMarkets.DoubleAuction.lemma_4_6
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T00:55:48.673488+00:00
-- url     : https://prove2.me/theorems/c67b2a97-0a80-4042-9069-29fb72555706
-- title:
--   Lemma 4.6 — for λ ≥ 4 a single global price p has WorstRationed(p) ≥ FB/40
-- statement:
--   For every double auction instance with $\lambda\ge4$ (4.1) there is a price $p\in[0,1]$ such that the worst-rationed rule with price $p$ satisfies
--   $$\mathrm{WorstRationed}(p)\ge\frac1{40}\,\mathrm{FB}.$$
--   The constant is $1/(4+4+32)$ from Lemmas 4.3–4.5.
--
--   Differences from the source:
--   - encoding: continuous F_1..F_n, G_1..G_m supported on [0, 1], all values and costs mutually independent → a `DAInstance n m`: no-atom probability measures with mass 1 on [0, 1]; expectations over the product `(Measure.pi μB).prod (Measure.pi μS)`; reason: same instances; independence is the product measure
--   - encoding: λ defined in (4.1) from the balanced price p̃ → a balanced price `pt` (`IsBalancedPrice`: pt ∈ [0, 1], E_v[B_pt] = E_c[S_pt]) as a variable, with λ = `expB pt`; reason: p̃ need not be unique but λ is the same for every balanced price, and a balanced price exists by continuity; quantifying over every one is at least as strong as fixing one
--   - encoding: 'there exists a worst-rationed rule with price p' → ∃ p ∈ [0, 1]; reason: prices live in the type space [0, 1]; requiring it only strengthens the existential
-- source:
--   Deng, Lin, Schoepflin, Wang, Stratifying Markets for Efficient Trade, STOC 2027 submission (manuscript sha256 49372bcf…), p. 32, Lemma 4.6

import Mathlib
import Definitions.Def_StratifyMarkets_DoubleAuction_Instance
import Definitions.Def_StratifyMarkets_DoubleAuction_WorstRationed
import Definitions.Def_StratifyMarkets_DoubleAuction_Prices

open MeasureTheory

namespace StratifyMarkets.DoubleAuction

/-- Lemma 4.6 (p. 32): if `λ ≥ 4`, some worst-rationed rule with a price `p ∈ [0, 1]` has
`WorstRationed(p) ≥ FB / 40`. -/
theorem lemma_4_6 {n m : ℕ} (I : DAInstance n m) (pt : ℝ)
    (hpt : I.IsBalancedPrice pt) (hlam : 4 ≤ I.expB pt) :
    ∃ p ∈ Set.Icc (0 : ℝ) 1, 1 / 40 * I.FB ≤ I.worstRationed p := by sorry

end StratifyMarkets.DoubleAuction
