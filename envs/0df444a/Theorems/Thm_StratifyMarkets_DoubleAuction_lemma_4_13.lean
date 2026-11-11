-- Prove2me | Theorems.Thm_StratifyMarkets_DoubleAuction_lemma_4_13
-- name    : StratifyMarkets.DoubleAuction.lemma_4_13
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T00:56:12.23969+00:00
-- url     : https://prove2.me/theorems/55d70717-4782-46a6-ba87-afaf90917883
-- title:
--   Lemma 4.13 — threshold price adjustment: SuperFP(t̄) ≥ (1 − e^{−1/4}) SuperFP(p) and WorstRationed(t̄) ≥ SuperFP(p)/7, symmetrically for t̲ (read with t̄ ∈ [p, m̄], t̲ ∈ [m̲, p])
-- statement:
--   Fix a double auction instance with $n,m\ge1$, a submarket $[a,b]$ ($0\le a<b\le1$) and a price $p\in[a,b]$.
--
--   *Buyer side.* If the expected number of buyers with values in $[p,b]$ is at least $1/4$, then for every $\bar t\in[p,b]$ with $\sum_i\Pr[\bar t\le v_i\le b]=1/4$,
--   $$\mathrm{SuperFP}(a,\bar t,b)\ge(1-e^{-1/4})\,\mathrm{SuperFP}(a,p,b),$$
--   and if moreover the expected number of sellers with costs in $[a,\bar t]$ is at most $1/4$, then $\mathrm{WorstRationed}(a,\bar t,b)\ge\frac17\mathrm{SuperFP}(a,p,b)$.
--
--   *Seller side.* If the expected number of sellers with costs in $[a,p]$ is at least $1/4$, then for every $\underline t\in[a,p]$ with $\sum_j\Pr[a\le c_j\le\underline t]=1/4$, $\mathrm{SuperFP}(a,\underline t,b)\ge(1-e^{-1/4})\mathrm{SuperFP}(a,p,b)$, and if moreover the expected number of buyers with values in $[\underline t,b]$ is at most $1/4$, then $\mathrm{WorstRationed}(a,\underline t,b)\ge\frac17\mathrm{SuperFP}(a,p,b)$.
--
--   The threshold is taken on the side of $p$ that the paper's proof chooses ("we can choose a threshold $\bar t\in[p,\overline m]$", p. 59); without it the printed statement fails (see the mission's insight I1). (Proof in Appendix A.3.)
--
--   Differences from the source:
--   - encoding: continuous F_1..F_n, G_1..G_m supported on [0, 1], all values and costs mutually independent → a `DAInstance n m`: no-atom probability measures with mass 1 on [0, 1]; expectations over the product `(Measure.pi μB).prod (Measure.pi μS)`; reason: same instances; independence is the product measure
--   - encoding: a submarket [m̲, m̄] with its price p (footnote 3) → reals a, b with 0 ≤ a < b ≤ 1 and p ∈ [a, b]; counts 'above p' / 'below p' within the submarket are Σ_i Pr[p ≤ v_i ≤ b] / Σ_j Pr[a ≤ c_j ≤ p]; reason: footnote 3's convention; closed intervals as in Remark 2.4
--   - encoding: the super buyer v_max = max_i v_i and super seller c_min = min_j c_j → instance arguments `[NeZero n] [NeZero m]` (n, m ≥ 1); reason: v_max and c_min are undefined without a buyer and a seller; the condition only excludes undefined cases
--   - reading: 'where t̄ is chosen so that the expected number of buyers with values above t̄ within this submarket is 1/4' (and symmetrically t̲) → every t̄ ∈ [p, b] with Σ_i Pr[t̄ ≤ v_i ≤ b] = 1/4, and every t̲ ∈ [a, p] with Σ_j Pr[a ≤ c_j ≤ t̲] = 1/4; reason: the proof chooses t̄ ∈ [p, m̄] (p. 59) and Lemmas 4.14, 4.15 use it so; for a t̄ < p with the same count both conclusions can fail (INSIGHTS.yaml I1); such a t̄ ∈ [p, b] exists by continuity
-- source:
--   Deng, Lin, Schoepflin, Wang, Stratifying Markets for Efficient Trade, STOC 2027 submission (manuscript sha256 49372bcf…), p. 37, Lemma 4.13 (proof App. A.3, pp. 59–60)

import Mathlib
import Definitions.Def_StratifyMarkets_DoubleAuction_Instance
import Definitions.Def_StratifyMarkets_DoubleAuction_WorstRationed
import Definitions.Def_StratifyMarkets_DoubleAuction_Submarket

open MeasureTheory

namespace StratifyMarkets.DoubleAuction

/-- Lemma 4.13 (p. 37), read with the threshold on the side of `p` that its proof chooses
(`t̄ ∈ [p, b]`, `t̲ ∈ [a, p]`, p. 59): inside a submarket `[a, b]` with price `p ∈ [a, b]`,
(buyer side) if the expected number of buyers with values in `[p, b]` is at least `1/4`, then every
`t̄ ∈ [p, b]` with expected number `1/4` of buyers in `[t̄, b]` has
`SuperFP(t̄) ≥ (1 − e^{−1/4}) SuperFP(p)`, and, if moreover the expected number of sellers with costs
in `[a, t̄]` is at most `1/4`, `WorstRationed(t̄) ≥ SuperFP(p) / 7`; (seller side) symmetrically. -/
theorem lemma_4_13 {n m : ℕ} [NeZero n] [NeZero m] (I : DAInstance n m) (a b p : ℝ)
    (ha : 0 ≤ a) (hab : a < b) (hb : b ≤ 1) (hap : a ≤ p) (hpb : p ≤ b) :
    (1 / 4 ≤ I.expBuyersIn p b → ∀ tB : ℝ, p ≤ tB → tB ≤ b → I.expBuyersIn tB b = 1 / 4 →
      (1 - Real.exp (-(1 / 4))) * I.superFP a p b ≤ I.superFP a tB b ∧
      (I.expSellersIn a tB ≤ 1 / 4 → 1 / 7 * I.superFP a p b ≤ I.worstRationedIn a tB b)) ∧
    (1 / 4 ≤ I.expSellersIn a p → ∀ tS : ℝ, a ≤ tS → tS ≤ p → I.expSellersIn a tS = 1 / 4 →
      (1 - Real.exp (-(1 / 4))) * I.superFP a p b ≤ I.superFP a tS b ∧
      (I.expBuyersIn tS b ≤ 1 / 4 → 1 / 7 * I.superFP a p b ≤ I.worstRationedIn a tS b)) := by sorry

end StratifyMarkets.DoubleAuction
