-- Prove2me | Theorems.Thm_StratifyMarkets_DoubleAuction_lemma_4_18
-- name    : StratifyMarkets.DoubleAuction.lemma_4_18
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T00:55:48.259234+00:00
-- url     : https://prove2.me/theorems/f3371894-a0c8-4709-a743-dddf474dc275
-- title:
--   Lemma 4.18 — with t̲ ≤ t̄, some refinement of the submarket has Strat ≥ (3/512) OneTrade(𝓑, 𝓢)
-- statement:
--   Fix a double auction instance, a submarket $[a,b]$ ($0\le a<b\le1$), a buyer threshold $\bar t$ and a seller threshold $\underline t$ of the submarket with $\underline t\le\bar t$. There is a refinement of $[a,b]$ — consecutive submarkets $a=r_0<r_1<\dots<r_K=b$ ($K\ge1$), a price $q_k\in[r_{k-1},r_k]$ in each, and the worst-rationed rule in each (Remark 4.19) — whose gains satisfy
--   $$\mathrm{Strat}=\sum_{k=1}^K\mathrm{WorstRationed}(r_{k-1},q_k,r_k)\ge\frac3{512}\,\mathrm{OneTrade}(\mathcal B,\mathcal S).$$
--   The constant is $\frac14\cdot\frac3{128}$.
--
--   Differences from the source:
--   - encoding: continuous F_1..F_n, G_1..G_m supported on [0, 1], all values and costs mutually independent → a `DAInstance n m`: no-atom probability measures with mass 1 on [0, 1]; expectations over the product `(Measure.pi μB).prod (Measure.pi μS)`; reason: same instances; independence is the product measure
--   - encoding: a submarket [m̲, m̄] (footnote 3) → reals a, b with 0 ≤ a < b ≤ 1; counts within the submarket are sums of Pr[lo ≤ v_i ≤ hi] / Pr[lo ≤ c_j ≤ hi] over closed intervals (E_v[A] = Σ_i Pr[q ≤ v_i ≤ t̄], E_c[T] = Σ_j Pr[t̲ ≤ c_j ≤ q]); reason: footnote 3's convention; closed intervals as in Remark 2.4; this lemma has no price p of its own
--   - encoding: the buyer threshold t̄ and seller threshold t̲ of the submarket → arbitrary tB, tS ∈ [a, b] with Σ_i Pr[tB ≤ v_i ≤ b] = 1/4 and Σ_j Pr[a ≤ c_j ≤ tS] = 1/4; reason: the thresholds need not be unique; quantifying over all of them is at least as strong as fixing one
--   - encoding: OneTrade(𝓑, 𝓢) = E[Σ_{i∈𝓑, j∈𝓢}(v_i − c_j) | B = 1 and S = 1] → E[Σ_{i∈𝓑, j∈𝓢}(v_i − c_j) · 1{B = 1, S = 1}] / Pr[B = 1 and S = 1]; reason: elementary conditional expectation; the denominator is at least 9/256 > 0 under the hypotheses, (4.21)
--   - encoding: a refinement of [m̲, m̄] (Remark 4.19) → a `Stratification` σ with σ.m 0 = a and σ.m (Fin.last σ.N) = b; Strat = `I.strat σ`; reason: a refinement is exactly a partition of [a, b] into consecutive submarkets with a price in each
--   - generalization: §4.2.1–4.2.2 (pp. 38, 40): the expected number of buyers and the expected number of sellers in the submarket are both greater than 1/4, which makes t̄ and t̲ well defined → no such hypothesis; the threshold equations (IsBuyerThreshold, IsSellerThreshold) are hypotheses, which imply both counts are at least 1/4, so the boundary instances with a count exactly 1/4 are also covered; reason: on every instance the source allows the statement is the source's; the condition serves only to make the thresholds exist, and the proofs (pp. 40–47) use only E_v[B] = E_c[S] = 1/4 and the order of t̄, t̲
-- source:
--   Deng, Lin, Schoepflin, Wang, Stratifying Markets for Efficient Trade, STOC 2027 submission (manuscript sha256 49372bcf…), p. 44, Lemma 4.18 (proof pp. 44–47; Remark 4.19)

import Mathlib
import Definitions.Def_StratifyMarkets_DoubleAuction_Instance
import Definitions.Def_StratifyMarkets_DoubleAuction_WorstRationed
import Definitions.Def_StratifyMarkets_DoubleAuction_Submarket

open MeasureTheory

namespace StratifyMarkets.DoubleAuction

/-- Lemma 4.18 (p. 44): inside a submarket `[a, b]` with thresholds `t̲ ≤ t̄`, some refinement of
`[a, b]` (Remark 4.19: consecutive submarkets `a = r₀ < r₁ < ⋯ < r_K = b`, a price in each, the
worst-rationed rule in each) has `Strat ≥ (3/512) OneTrade(𝓑, 𝓢)`. -/
theorem lemma_4_18 {n m : ℕ} (I : DAInstance n m) (a b tB tS : ℝ)
    (ha : 0 ≤ a) (hab : a < b) (hb : b ≤ 1)
    (htB : I.IsBuyerThreshold a b tB) (htS : I.IsSellerThreshold a b tS) (hle : tS ≤ tB) :
    ∃ σ : Stratification, σ.m 0 = a ∧ σ.m (Fin.last σ.N) = b ∧
      3 / 512 * I.oneTrade a b tB tS ≤ I.strat σ := by sorry

end StratifyMarkets.DoubleAuction
