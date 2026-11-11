-- Prove2me | Theorems.Thm_StratifyMarkets_DoubleAuction_lemma_4_17
-- name    : StratifyMarkets.DoubleAuction.lemma_4_17
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T00:56:32.177869+00:00
-- url     : https://prove2.me/theorems/77c8b285-eaa7-46be-8559-1ebde38b3010
-- title:
--   Lemma 4.17 — with t̲ ≤ t̄ and a price q ∈ [t̲, t̄] with E[A], E[T] ≤ 1/4, WorstRationed(q) ≥ (3/128) OneTrade(𝓑, 𝓢)
-- statement:
--   Fix a double auction instance, a submarket $[a,b]$ ($0\le a<b\le1$), a buyer threshold $\bar t$ and a seller threshold $\underline t$ of the submarket with $\underline t\le\bar t$, and a price $q\in[\underline t,\bar t]$. Let $A$ be the number of buyers with values in $[q,\bar t]$ and $T$ the number of sellers with costs in $[\underline t,q]$. If $\mathbb E_{\mathbf v}[A]\le1/4$ and $\mathbb E_{\mathbf c}[T]\le1/4$, then
--   $$\mathrm{WorstRationed}(a,q,b)\ge\frac3{128}\,\mathrm{OneTrade}(\mathcal B,\mathcal S).$$
--   The constant is $\frac23\cdot\frac9{256}$.
--
--   Differences from the source:
--   - encoding: continuous F_1..F_n, G_1..G_m supported on [0, 1], all values and costs mutually independent → a `DAInstance n m`: no-atom probability measures with mass 1 on [0, 1]; expectations over the product `(Measure.pi μB).prod (Measure.pi μS)`; reason: same instances; independence is the product measure
--   - encoding: a submarket [m̲, m̄] (footnote 3) → reals a, b with 0 ≤ a < b ≤ 1; counts within the submarket are sums of Pr[lo ≤ v_i ≤ hi] / Pr[lo ≤ c_j ≤ hi] over closed intervals (E_v[A] = Σ_i Pr[q ≤ v_i ≤ t̄], E_c[T] = Σ_j Pr[t̲ ≤ c_j ≤ q]); reason: footnote 3's convention; closed intervals as in Remark 2.4; this lemma has no price p of its own
--   - encoding: the buyer threshold t̄ and seller threshold t̲ of the submarket → arbitrary tB, tS ∈ [a, b] with Σ_i Pr[tB ≤ v_i ≤ b] = 1/4 and Σ_j Pr[a ≤ c_j ≤ tS] = 1/4; reason: the thresholds need not be unique; quantifying over all of them is at least as strong as fixing one
--   - encoding: OneTrade(𝓑, 𝓢) = E[Σ_{i∈𝓑, j∈𝓢}(v_i − c_j) | B = 1 and S = 1] → E[Σ_{i∈𝓑, j∈𝓢}(v_i − c_j) · 1{B = 1, S = 1}] / Pr[B = 1 and S = 1]; reason: elementary conditional expectation; the denominator is at least 9/256 > 0 under the hypotheses, (4.21)
--   - encoding: 'if there exists a price q between t̲ and t̄ such that E_v[A] ≤ 1/4 and E_c[T] ≤ 1/4, then WorstRationed(q) ≥ …' → for every q with t̲ ≤ q ≤ t̄, Σ_i Pr[q ≤ v_i ≤ t̄] ≤ 1/4 and Σ_j Pr[t̲ ≤ c_j ≤ q] ≤ 1/4 imply the bound at that q; reason: the conclusion is about the q of the hypothesis
--   - generalization: §4.2.1–4.2.2 (pp. 38, 40): the expected number of buyers and the expected number of sellers in the submarket are both greater than 1/4, which makes t̄ and t̲ well defined → no such hypothesis; the threshold equations (IsBuyerThreshold, IsSellerThreshold) are hypotheses, which imply both counts are at least 1/4, so the boundary instances with a count exactly 1/4 are also covered; reason: on every instance the source allows the statement is the source's; the condition serves only to make the thresholds exist, and the proofs (pp. 40–47) use only E_v[B] = E_c[S] = 1/4 and the order of t̄, t̲
-- source:
--   Deng, Lin, Schoepflin, Wang, Stratifying Markets for Efficient Trade, STOC 2027 submission (manuscript sha256 49372bcf…), p. 42, Lemma 4.17

import Mathlib
import Definitions.Def_StratifyMarkets_DoubleAuction_Instance
import Definitions.Def_StratifyMarkets_DoubleAuction_WorstRationed
import Definitions.Def_StratifyMarkets_DoubleAuction_Submarket

open MeasureTheory

namespace StratifyMarkets.DoubleAuction

/-- Lemma 4.17 (p. 42): inside a submarket `[a, b]` with thresholds `t̲ ≤ t̄`, if a price
`q ∈ [t̲, t̄]` has `E_𝐯[A] ≤ 1/4` (buyers with values in `[q, t̄]`) and `E_𝐜[T] ≤ 1/4` (sellers with
costs in `[t̲, q]`), then `WorstRationed(a, q, b) ≥ (3/128) OneTrade(𝓑, 𝓢)`. -/
theorem lemma_4_17 {n m : ℕ} (I : DAInstance n m) (a b tB tS q : ℝ)
    (ha : 0 ≤ a) (hab : a < b) (hb : b ≤ 1)
    (htB : I.IsBuyerThreshold a b tB) (htS : I.IsSellerThreshold a b tS) (hle : tS ≤ tB)
    (hq1 : tS ≤ q) (hq2 : q ≤ tB)
    (hA : I.expBuyersIn q tB ≤ 1 / 4) (hT : I.expSellersIn tS q ≤ 1 / 4) :
    3 / 128 * I.oneTrade a b tB tS ≤ I.worstRationedIn a q b := by sorry

end StratifyMarkets.DoubleAuction
