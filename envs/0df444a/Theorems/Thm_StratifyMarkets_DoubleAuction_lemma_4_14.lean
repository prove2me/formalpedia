-- Prove2me | Theorems.Thm_StratifyMarkets_DoubleAuction_lemma_4_14
-- name    : StratifyMarkets.DoubleAuction.lemma_4_14
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T00:56:10.404143+00:00
-- url     : https://prove2.me/theorems/8a0168d1-954f-4fea-a7ef-8a80aeb61df6
-- title:
--   Lemma 4.14 — if one side of a submarket has expected participation at most 1/4, some price p′ has WorstRationed(p′) ≥ SuperFP(p)/7
-- statement:
--   Fix a double auction instance with $n,m\ge1$, a submarket $[a,b]$ ($0\le a<b\le1$) and a price $p\in[a,b]$. If the expected number of buyers in the submarket, $\sum_i\Pr[a\le v_i\le b]$, or the expected number of sellers in the submarket, $\sum_j\Pr[a\le c_j\le b]$, is at most $1/4$, then there is a price $p'\in[a,b]$ such that
--   $$\mathrm{WorstRationed}(a,p',b)\ge\frac17\,\mathrm{SuperFP}(a,p,b).$$
--
--   Differences from the source:
--   - encoding: continuous F_1..F_n, G_1..G_m supported on [0, 1], all values and costs mutually independent → a `DAInstance n m`: no-atom probability measures with mass 1 on [0, 1]; expectations over the product `(Measure.pi μB).prod (Measure.pi μS)`; reason: same instances; independence is the product measure
--   - encoding: a submarket [m̲, m̄] with its price p (footnote 3) → reals a, b with 0 ≤ a < b ≤ 1 and p ∈ [a, b]; counts 'above p' / 'below p' within the submarket are Σ_i Pr[p ≤ v_i ≤ b] / Σ_j Pr[a ≤ c_j ≤ p]; reason: footnote 3's convention; closed intervals as in Remark 2.4
--   - encoding: the super buyer v_max = max_i v_i and super seller c_min = min_j c_j → instance arguments `[NeZero n] [NeZero m]` (n, m ≥ 1); reason: v_max and c_min are undefined without a buyer and a seller; the condition only excludes undefined cases
--   - encoding: 'there exists a price such that the corresponding worst-rationed rule achieves …' → ∃ p' ∈ [a, b] with WorstRationed(a, p', b) ≥ SuperFP(a, p, b)/7; reason: footnote 3: prices lie within the submarket
-- source:
--   Deng, Lin, Schoepflin, Wang, Stratifying Markets for Efficient Trade, STOC 2027 submission (manuscript sha256 49372bcf…), p. 38, Lemma 4.14

import Mathlib
import Definitions.Def_StratifyMarkets_DoubleAuction_Instance
import Definitions.Def_StratifyMarkets_DoubleAuction_WorstRationed
import Definitions.Def_StratifyMarkets_DoubleAuction_Submarket

open MeasureTheory

namespace StratifyMarkets.DoubleAuction

/-- Lemma 4.14 (p. 38): inside a submarket `[a, b]` with price `p ∈ [a, b]`, if the expected number
of buyers in the submarket or the expected number of sellers in the submarket is at most `1/4`, some
price `p' ∈ [a, b]` has `WorstRationed(a, p', b) ≥ SuperFP(a, p, b) / 7`. -/
theorem lemma_4_14 {n m : ℕ} [NeZero n] [NeZero m] (I : DAInstance n m) (a b p : ℝ)
    (ha : 0 ≤ a) (hab : a < b) (hb : b ≤ 1) (hap : a ≤ p) (hpb : p ≤ b)
    (hlow : I.expBuyersIn a b ≤ 1 / 4 ∨ I.expSellersIn a b ≤ 1 / 4) :
    ∃ p' ∈ Set.Icc a b, 1 / 7 * I.superFP a p b ≤ I.worstRationedIn a p' b := by sorry

end StratifyMarkets.DoubleAuction
