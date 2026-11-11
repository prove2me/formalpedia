-- Prove2me | Theorems.Thm_StratifyMarkets_DoubleAuction_lemma_4_8
-- name    : StratifyMarkets.DoubleAuction.lemma_4_8
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T00:52:20.468056+00:00
-- url     : https://prove2.me/theorems/cc6a2271-f29f-4ab1-ae40-1480bda14d51
-- title:
--   Lemma 4.8 — Bernoulli tail comparison: E[X] ≤ E[Y] < 4 implies Pr[1 + X ≤ Y] ≥ (1/7) Pr[max{1 + X, Y} > 5]
-- statement:
--   Let $X$ and $Y$ be independent random variables, each a sum of independent Bernoulli random variables: $X=\sum_{i=1}^lX_i$ and $Y=\sum_{j=1}^rY_j$ with arbitrary success probabilities. If $\mathbb E[X]\le\mathbb E[Y]<4$, then
--   $$\Pr[1+X\le Y]\ge\frac17\,\Pr\big[\max\{1+X,Y\}>5\big].$$
--   It is the probability comparison behind Lemma 4.10 (proof in Appendix A.1).
--
--   Differences from the source:
--   - encoding: two independent random variables X, Y, each a sum of independent Bernoulli random variables → families X : Fin l → Ω → ℝ, Y : Fin r → Ω → ℝ, each measurable, a.s. {0, 1}-valued and `iIndepFun`, with `IndepFun (Σ X_i) (Σ Y_j)`; reason: exactly the printed hypotheses; any l, r ≥ 0
-- source:
--   Deng, Lin, Schoepflin, Wang, Stratifying Markets for Efficient Trade, STOC 2027 submission (manuscript sha256 49372bcf…), p. 32, Lemma 4.8 (proof App. A.1, pp. 56–57)

import Mathlib

open MeasureTheory

namespace StratifyMarkets.DoubleAuction

/-- Lemma 4.8 (p. 32): if `X = Σ_{i<l} X_i` and `Y = Σ_{j<r} Y_j` are independent, each a sum of
independent Bernoulli random variables, and `E[X] ≤ E[Y] < 4`, then
`Pr[1 + X ≤ Y] ≥ (1/7) Pr[max{1 + X, Y} > 5]`. -/
theorem lemma_4_8 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (l r : ℕ) (X : Fin l → Ω → ℝ) (Y : Fin r → Ω → ℝ)
    (hXm : ∀ i, Measurable (X i)) (hYm : ∀ j, Measurable (Y j))
    (hXb : ∀ i, ∀ᵐ ω ∂P, X i ω = 0 ∨ X i ω = 1) (hYb : ∀ j, ∀ᵐ ω ∂P, Y j ω = 0 ∨ Y j ω = 1)
    (hXi : ProbabilityTheory.iIndepFun X P) (hYi : ProbabilityTheory.iIndepFun Y P)
    (hXY : ProbabilityTheory.IndepFun (fun ω => ∑ i, X i ω) (fun ω => ∑ j, Y j ω) P)
    (hmean : ∫ ω, ∑ i, X i ω ∂P ≤ ∫ ω, ∑ j, Y j ω ∂P) (hfour : ∫ ω, ∑ j, Y j ω ∂P < 4) :
    (1 / 7 : ENNReal) * P {ω | 5 < max (1 + ∑ i, X i ω) (∑ j, Y j ω)} ≤
      P {ω | 1 + ∑ i, X i ω ≤ ∑ j, Y j ω} := by sorry

end StratifyMarkets.DoubleAuction
