-- Prove2me | Theorems.Thm_StratifyMarkets_DoubleAuction_lemma_4_16
-- name    : StratifyMarkets.DoubleAuction.lemma_4_16
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T00:54:05.103205+00:00
-- url     : https://prove2.me/theorems/b7a70ebe-a271-4d09-838e-24622effcf57
-- title:
--   Lemma 4.16 — single-pair benchmark: with t̲ ≤ t̄, OneTrade(𝓑, 𝓢) ≥ SuperFP(p)
-- statement:
--   Fix a double auction instance with $n,m\ge1$, a submarket $[a,b]$ ($0\le a<b\le1$), a price $p\in[a,b]$, a buyer threshold $\bar t$ and a seller threshold $\underline t$ of the submarket with $\underline t\le\bar t$. With $\mathcal B=\{i:\bar t\le v_i\le b\}$, $\mathcal S=\{j:a\le c_j\le\underline t\}$, $B=|\mathcal B|$, $S=|\mathcal S|$,
--   $$\mathrm{OneTrade}(\mathcal B,\mathcal S)=\mathbb E\Big[\sum_{i\in\mathcal B,j\in\mathcal S}(v_i-c_j)\Big|B=1,S=1\Big]\ge\mathrm{SuperFP}(a,p,b).$$
--
--   Differences from the source:
--   - encoding: continuous F_1..F_n, G_1..G_m supported on [0, 1], all values and costs mutually independent → a `DAInstance n m`: no-atom probability measures with mass 1 on [0, 1]; expectations over the product `(Measure.pi μB).prod (Measure.pi μS)`; reason: same instances; independence is the product measure
--   - encoding: a submarket [m̲, m̄] with its price p (footnote 3) → reals a, b with 0 ≤ a < b ≤ 1 and p ∈ [a, b]; counts 'above p' / 'below p' within the submarket are Σ_i Pr[p ≤ v_i ≤ b] / Σ_j Pr[a ≤ c_j ≤ p]; reason: footnote 3's convention; closed intervals as in Remark 2.4
--   - encoding: the super buyer v_max = max_i v_i and super seller c_min = min_j c_j → instance arguments `[NeZero n] [NeZero m]` (n, m ≥ 1); reason: v_max and c_min are undefined without a buyer and a seller; the condition only excludes undefined cases
--   - encoding: the buyer threshold t̄ and seller threshold t̲ of the submarket → arbitrary tB, tS ∈ [a, b] with Σ_i Pr[tB ≤ v_i ≤ b] = 1/4 and Σ_j Pr[a ≤ c_j ≤ tS] = 1/4; reason: the thresholds need not be unique; quantifying over all of them is at least as strong as fixing one
--   - encoding: OneTrade(𝓑, 𝓢) = E[Σ_{i∈𝓑, j∈𝓢}(v_i − c_j) | B = 1 and S = 1] → E[Σ_{i∈𝓑, j∈𝓢}(v_i − c_j) · 1{B = 1, S = 1}] / Pr[B = 1 and S = 1]; reason: elementary conditional expectation; the denominator is at least 9/256 > 0 under the hypotheses, (4.21)
--   - generalization: §4.2.1–4.2.2 (pp. 38, 40): the expected number of buyers and the expected number of sellers in the submarket are both greater than 1/4, which makes t̄ and t̲ well defined → no such hypothesis; the threshold equations (IsBuyerThreshold, IsSellerThreshold) are hypotheses, which imply both counts are at least 1/4, so the boundary instances with a count exactly 1/4 are also covered; reason: on every instance the source allows the statement is the source's; the condition serves only to make the thresholds exist, and the proofs (pp. 40–47) use only E_v[B] = E_c[S] = 1/4 and the order of t̄, t̲
-- source:
--   Deng, Lin, Schoepflin, Wang, Stratifying Markets for Efficient Trade, STOC 2027 submission (manuscript sha256 49372bcf…), p. 40, Lemma 4.16

import Mathlib
import Definitions.Def_StratifyMarkets_DoubleAuction_Instance
import Definitions.Def_StratifyMarkets_DoubleAuction_Submarket

open MeasureTheory

namespace StratifyMarkets.DoubleAuction

/-- Lemma 4.16 (p. 40): inside a submarket `[a, b]` with price `p ∈ [a, b]` and thresholds
`t̲ ≤ t̄`, `OneTrade(𝓑, 𝓢) ≥ SuperFP(a, p, b)`. -/
theorem lemma_4_16 {n m : ℕ} [NeZero n] [NeZero m] (I : DAInstance n m) (a b p tB tS : ℝ)
    (ha : 0 ≤ a) (hab : a < b) (hb : b ≤ 1) (hap : a ≤ p) (hpb : p ≤ b)
    (htB : I.IsBuyerThreshold a b tB) (htS : I.IsSellerThreshold a b tS) (hle : tS ≤ tB) :
    I.superFP a p b ≤ I.oneTrade a b tB tS := by sorry

end StratifyMarkets.DoubleAuction
