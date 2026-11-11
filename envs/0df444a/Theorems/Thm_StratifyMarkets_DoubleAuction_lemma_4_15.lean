-- Prove2me | Theorems.Thm_StratifyMarkets_DoubleAuction_lemma_4_15
-- name    : StratifyMarkets.DoubleAuction.lemma_4_15
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T00:56:21.48521+00:00
-- url     : https://prove2.me/theorems/7ed0c926-992d-4443-baec-395e54c952cc
-- title:
--   Lemma 4.15 — if the buyer threshold t̄ is below the seller threshold t̲, some price p′ has WorstRationed(p′) ≥ SuperFP(p)/7
-- statement:
--   Fix a double auction instance with $n,m\ge1$, a submarket $[a,b]$ ($0\le a<b\le1$) and a price $p\in[a,b]$. Let $\bar t\in[a,b]$ be a buyer threshold ($\sum_i\Pr[\bar t\le v_i\le b]=1/4$) and $\underline t\in[a,b]$ a seller threshold ($\sum_j\Pr[a\le c_j\le\underline t]=1/4$). If $\bar t<\underline t$, then there is a price $p'\in[a,b]$ with
--   $$\mathrm{WorstRationed}(a,p',b)\ge\frac17\,\mathrm{SuperFP}(a,p,b).$$
--
--   Differences from the source:
--   - encoding: continuous F_1..F_n, G_1..G_m supported on [0, 1], all values and costs mutually independent → a `DAInstance n m`: no-atom probability measures with mass 1 on [0, 1]; expectations over the product `(Measure.pi μB).prod (Measure.pi μS)`; reason: same instances; independence is the product measure
--   - encoding: a submarket [m̲, m̄] with its price p (footnote 3) → reals a, b with 0 ≤ a < b ≤ 1 and p ∈ [a, b]; counts 'above p' / 'below p' within the submarket are Σ_i Pr[p ≤ v_i ≤ b] / Σ_j Pr[a ≤ c_j ≤ p]; reason: footnote 3's convention; closed intervals as in Remark 2.4
--   - encoding: the super buyer v_max = max_i v_i and super seller c_min = min_j c_j → instance arguments `[NeZero n] [NeZero m]` (n, m ≥ 1); reason: v_max and c_min are undefined without a buyer and a seller; the condition only excludes undefined cases
--   - encoding: the buyer threshold t̄ and seller threshold t̲ of the submarket → arbitrary tB, tS ∈ [a, b] with Σ_i Pr[tB ≤ v_i ≤ b] = 1/4 and Σ_j Pr[a ≤ c_j ≤ tS] = 1/4; reason: the thresholds need not be unique; quantifying over all of them is at least as strong as fixing one
--   - encoding: 'there exists a price such that …' → ∃ p' ∈ [a, b]; reason: footnote 3: prices lie within the submarket
--   - generalization: §4.2.1–4.2.2 (pp. 38, 40): the expected number of buyers and the expected number of sellers in the submarket are both greater than 1/4, which makes t̄ and t̲ well defined → no such hypothesis; the threshold equations (IsBuyerThreshold, IsSellerThreshold) are hypotheses, which imply both counts are at least 1/4, so the boundary instances with a count exactly 1/4 are also covered; reason: on every instance the source allows the statement is the source's; the condition serves only to make the thresholds exist, and the proofs (pp. 40–47) use only E_v[B] = E_c[S] = 1/4 and the order of t̄, t̲
-- source:
--   Deng, Lin, Schoepflin, Wang, Stratifying Markets for Efficient Trade, STOC 2027 submission (manuscript sha256 49372bcf…), p. 38, Lemma 4.15

import Mathlib
import Definitions.Def_StratifyMarkets_DoubleAuction_Instance
import Definitions.Def_StratifyMarkets_DoubleAuction_WorstRationed
import Definitions.Def_StratifyMarkets_DoubleAuction_Submarket

open MeasureTheory

namespace StratifyMarkets.DoubleAuction

/-- Lemma 4.15 (p. 38): inside a submarket `[a, b]` with price `p ∈ [a, b]`, if the buyer threshold
`t̄` is below the seller threshold `t̲`, some price `p' ∈ [a, b]` has
`WorstRationed(a, p', b) ≥ SuperFP(a, p, b) / 7`. -/
theorem lemma_4_15 {n m : ℕ} [NeZero n] [NeZero m] (I : DAInstance n m) (a b p tB tS : ℝ)
    (ha : 0 ≤ a) (hab : a < b) (hb : b ≤ 1) (hap : a ≤ p) (hpb : p ≤ b)
    (htB : I.IsBuyerThreshold a b tB) (htS : I.IsSellerThreshold a b tS) (hlt : tB < tS) :
    ∃ p' ∈ Set.Icc a b, 1 / 7 * I.superFP a p b ≤ I.worstRationedIn a p' b := by sorry

end StratifyMarkets.DoubleAuction
