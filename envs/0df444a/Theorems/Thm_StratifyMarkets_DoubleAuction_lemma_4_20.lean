-- Prove2me | Theorems.Thm_StratifyMarkets_DoubleAuction_lemma_4_20
-- name    : StratifyMarkets.DoubleAuction.lemma_4_20
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T00:55:57.947721+00:00
-- url     : https://prove2.me/theorems/46c5bd37-fabe-441b-adf8-c9269bfaba8f
-- title:
--   Lemma 4.20 — some stratification has Strat ≥ E[RealizedFB · 1{τ ≤ 5}] / (10240e)
-- statement:
--   For every double auction instance there is a market stratification (Definition 2.3), running the worst-rationed rule in each submarket, such that
--   $$\mathrm{Strat}\ge\frac1{10240e}\,\mathbb E_{\mathbf v,\mathbf c}\big[\mathrm{RealizedFB}\cdot\mathbb 1\{\tau\le5\}\big].$$
--   The constant is $\frac15\cdot\frac1{12e}\cdot\frac3{512}$; this is Step 2 of the double-auction argument.
--
--   Differences from the source:
--   - encoding: continuous F_1..F_n, G_1..G_m supported on [0, 1], all values and costs mutually independent → a `DAInstance n m`: no-atom probability measures with mass 1 on [0, 1]; expectations over the product `(Measure.pi μB).prod (Measure.pi μS)`; reason: same instances; independence is the product measure
--   - encoding: indices k = 1, …, N → 0-based `k : Fin N`, submarket k is [m k.castSucc, m k.succ] with price p k; reason: relabelling only
-- source:
--   Deng, Lin, Schoepflin, Wang, Stratifying Markets for Efficient Trade, STOC 2027 submission (manuscript sha256 49372bcf…), p. 48, Lemma 4.20

import Mathlib
import Definitions.Def_StratifyMarkets_DoubleAuction_Instance
import Definitions.Def_StratifyMarkets_DoubleAuction_WorstRationed

open MeasureTheory

namespace StratifyMarkets.DoubleAuction

/-- Lemma 4.20 (p. 48): every double auction instance has a stratification, running the
worst-rationed rule in each submarket, with `Strat ≥ E[RealizedFB · 1{τ ≤ 5}] / (10240 e)`. -/
theorem lemma_4_20 {n m : ℕ} (I : DAInstance n m) :
    ∃ σ : Stratification, 1 / (10240 * Real.exp 1) * I.FBtauLe5 ≤ I.strat σ := by sorry

end StratifyMarkets.DoubleAuction
