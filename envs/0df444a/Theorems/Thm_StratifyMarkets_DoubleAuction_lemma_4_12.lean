-- Prove2me | Theorems.Thm_StratifyMarkets_DoubleAuction_lemma_4_12
-- name    : StratifyMarkets.DoubleAuction.lemma_4_12
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T00:55:56.1112+00:00
-- url     : https://prove2.me/theorems/7b43ddd7-b975-4729-9c60-1aa2d82b52f8
-- title:
--   Lemma 4.12 — inside a submarket, low expected participation on both sides gives WorstRationed(p) ≥ (3/4) SuperFP(p)
-- statement:
--   Fix a double auction instance with $n,m\ge1$, a submarket $[\underline m,\overline m]=[a,b]$ with $0\le a<b\le1$ and a price $p\in[a,b]$. If the expected number of buyers with values in $[p,b]$ and the expected number of sellers with costs in $[a,p]$ are both at most $1/4$, then
--   $$\mathrm{WorstRationed}(a,p,b)\ge\frac34\,\mathrm{SuperFP}(a,p,b).$$
--   (Proof in Appendix A.2.)
--
--   Differences from the source:
--   - encoding: continuous F_1..F_n, G_1..G_m supported on [0, 1], all values and costs mutually independent → a `DAInstance n m`: no-atom probability measures with mass 1 on [0, 1]; expectations over the product `(Measure.pi μB).prod (Measure.pi μS)`; reason: same instances; independence is the product measure
--   - encoding: a submarket [m̲, m̄] with its price p (footnote 3) → reals a, b with 0 ≤ a < b ≤ 1 and p ∈ [a, b]; counts 'above p' / 'below p' within the submarket are Σ_i Pr[p ≤ v_i ≤ b] / Σ_j Pr[a ≤ c_j ≤ p]; reason: footnote 3's convention; closed intervals as in Remark 2.4
--   - encoding: the super buyer v_max = max_i v_i and super seller c_min = min_j c_j → instance arguments `[NeZero n] [NeZero m]` (n, m ≥ 1); reason: v_max and c_min are undefined without a buyer and a seller; the condition only excludes undefined cases
-- source:
--   Deng, Lin, Schoepflin, Wang, Stratifying Markets for Efficient Trade, STOC 2027 submission (manuscript sha256 49372bcf…), p. 36, Lemma 4.12 (proof App. A.2, pp. 57–59)

import Mathlib
import Definitions.Def_StratifyMarkets_DoubleAuction_Instance
import Definitions.Def_StratifyMarkets_DoubleAuction_WorstRationed
import Definitions.Def_StratifyMarkets_DoubleAuction_Submarket

open MeasureTheory

namespace StratifyMarkets.DoubleAuction

/-- Lemma 4.12 (p. 36): inside a submarket `[a, b]` with price `p ∈ [a, b]`, if the expected number
of buyers with values in `[p, b]` and the expected number of sellers with costs in `[a, p]` are both
at most `1/4`, then `WorstRationed(a, p, b) ≥ (3/4) SuperFP(a, p, b)`. -/
theorem lemma_4_12 {n m : ℕ} [NeZero n] [NeZero m] (I : DAInstance n m) (a b p : ℝ)
    (ha : 0 ≤ a) (hab : a < b) (hb : b ≤ 1) (hap : a ≤ p) (hpb : p ≤ b)
    (hB : I.expBuyersIn p b ≤ 1 / 4) (hS : I.expSellersIn a p ≤ 1 / 4) :
    3 / 4 * I.superFP a p b ≤ I.worstRationedIn a p b := by sorry

end StratifyMarkets.DoubleAuction
