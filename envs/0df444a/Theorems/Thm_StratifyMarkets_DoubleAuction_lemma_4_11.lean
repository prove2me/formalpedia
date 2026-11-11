-- Prove2me | Theorems.Thm_StratifyMarkets_DoubleAuction_lemma_4_11
-- name    : StratifyMarkets.DoubleAuction.lemma_4_11
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T00:56:13.684888+00:00
-- url     : https://prove2.me/theorems/ee045c8b-7ea3-41c3-a51c-b7a26d136b5d
-- title:
--   Lemma 4.11 — a single-submarket stratification with Strat ≥ FB/40 if λ ≥ 4, ≥ (1/7)E[RealizedFB·1{τ>5}] if λ < 4, hence ≥ (1/40)E[RealizedFB·1{τ>5}]
-- statement:
--   For every double auction instance there is a stratification with the single submarket $[0,1]$ (and a price $p\in[0,1]$), running the worst-rationed rule, such that
--   $$\mathrm{Strat}\ge\frac1{40}\mathrm{FB}\ \text{ if }\lambda\ge4\qquad\text{and}\qquad\mathrm{Strat}\ge\frac17\,\mathbb E_{\mathbf v,\mathbf c}\big[\mathrm{RealizedFB}\cdot\mathbb 1\{\tau>5\}\big]\ \text{ if }\lambda<4;$$
--   in particular $\mathrm{Strat}\ge\frac1{40}\mathbb E_{\mathbf v,\mathbf c}[\mathrm{RealizedFB}\cdot\mathbb 1\{\tau>5\}]$ for every instance. Here $\mathrm{Strat}=\mathrm{WorstRationed}(0,p,1)$. This is Step 1 of the double-auction argument.
--
--   Differences from the source:
--   - encoding: continuous F_1..F_n, G_1..G_m supported on [0, 1], all values and costs mutually independent → a `DAInstance n m`: no-atom probability measures with mass 1 on [0, 1]; expectations over the product `(Measure.pi μB).prod (Measure.pi μS)`; reason: same instances; independence is the product measure
--   - encoding: a stratification with the single submarket [0, 1] → a price p ∈ [0, 1] with Strat = `worstRationedIn 0 p 1`; reason: the stratification N = 1, m₀ = 0, m₁ = 1, p₁ = p has exactly these gains
--   - encoding: the case split on λ ≥ 4 / λ < 4 → for every balanced price pt, the two implications on `expB pt`; the price p is chosen before pt; reason: λ is the same for every balanced price; this order is at least as strong
--   - encoding: 'In particular, …' → a third conjunct for the same p; reason: every clause of the printed statement is stated
-- source:
--   Deng, Lin, Schoepflin, Wang, Stratifying Markets for Efficient Trade, STOC 2027 submission (manuscript sha256 49372bcf…), p. 34, Lemma 4.11

import Mathlib
import Definitions.Def_StratifyMarkets_DoubleAuction_Instance
import Definitions.Def_StratifyMarkets_DoubleAuction_WorstRationed
import Definitions.Def_StratifyMarkets_DoubleAuction_Prices

open MeasureTheory

namespace StratifyMarkets.DoubleAuction

/-- Lemma 4.11 (p. 34): there is one price `p ∈ [0, 1]` such that the stratification with the
single submarket `[0, 1]` and price `p`, whose gains are `WorstRationed(0, p, 1)`, has
`Strat ≥ FB / 40` if `λ ≥ 4` and `Strat ≥ (1/7) E[RealizedFB · 1{τ > 5}]` if `λ < 4`; in
particular `Strat ≥ (1/40) E[RealizedFB · 1{τ > 5}]`. -/
theorem lemma_4_11 {n m : ℕ} (I : DAInstance n m) :
    ∃ p ∈ Set.Icc (0 : ℝ) 1,
      (∀ pt : ℝ, I.IsBalancedPrice pt →
        (4 ≤ I.expB pt → 1 / 40 * I.FB ≤ I.worstRationedIn 0 p 1) ∧
        (I.expB pt < 4 → 1 / 7 * I.FBtauGt5 ≤ I.worstRationedIn 0 p 1)) ∧
      1 / 40 * I.FBtauGt5 ≤ I.worstRationedIn 0 p 1 := by sorry

end StratifyMarkets.DoubleAuction
