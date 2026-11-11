-- Prove2me | Theorems.Thm_StratifyMarkets_DoubleAuction_theorem_4_2
-- name    : StratifyMarkets.DoubleAuction.theorem_4_2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T00:52:17.186197+00:00
-- url     : https://prove2.me/theorems/93eb0e4e-fe40-43b7-934b-591c1d488e89
-- title:
--   Theorem 4.2 [JS68] — mean–median inequality for sums of independent Bernoulli random variables
-- statement:
--   Let $X=\sum_{i=1}^{l}X_i$ be a sum of $l\ge0$ independent Bernoulli random variables (arbitrary, possibly different success probabilities) on a probability space. If the mean of $X$ lies between the integers $k$ and $k+1$, then a median of $X$ is $k$ or $k+1$; equivalently,
--   $$\Pr\big[X>\mathbb E[X]-1\big]\ge\tfrac12\qquad\text{and}\qquad\Pr\big[X<\mathbb E[X]+1\big]\ge\tfrac12.$$
--   This is a cited result of Jogdeo and Samuels [JS68], used throughout §4 (Lemmas 4.4, 4.5, 4.8).
--
--   **Formalization Note.** A median of $X$ is an $M$ with $\Pr[X\le M]\ge1/2$ and $\Pr[X\ge M]\ge1/2$. The statement is the conjunction of the median clause (for every integer $k$ with $k\le\mathbb E[X]\le k+1$, some $M\in\{k,k+1\}$ is a median) and both displayed inequalities. Each $X_i$ is measurable and almost surely $0$ or $1$, and the family is `iIndepFun`.
--
--   Differences from the source:
--   - reading: 'a median of X is either k or k + 1' → some M ∈ {k, k + 1} is a median (Pr[X ≤ M] ≥ 1/2 and Pr[X ≥ M] ≥ 1/2); reason: the universal reading 'every median is k or k + 1' is false (for one Bernoulli(1/2) every point of [0, 1] is a median); the existential reading is the theorem of [JS68]
--   - reading: the mean 'between the integers k and k + 1' → k ≤ E[X] ≤ k + 1 with k ∈ ℤ (closed); reason: the closed reading also covers an integer mean, so it is at least as strong as the open one
--   - encoding: a sum of independent Bernoulli random variables → X = Σ_{i<l} X_i with X_i measurable, a.s. in {0, 1}, mutually independent (`iIndepFun`), any l ≥ 0; reason: same objects
--   - encoding: 'Equivalently, …' → the median clause and both displayed inequalities as one conjunction; reason: every clause of the printed statement is stated
-- source:
--   Deng, Lin, Schoepflin, Wang, Stratifying Markets for Efficient Trade, STOC 2027 submission (manuscript sha256 49372bcf…), p. 26, Theorem 4.2 (cited: [JS68])

import Mathlib

open MeasureTheory

namespace StratifyMarkets.DoubleAuction

/-- Theorem 4.2 [JS68] (p. 26): let `X = Σ_{i<l} X_i` be a sum of independent Bernoulli random
variables. If `k ≤ E[X] ≤ k + 1` for an integer `k`, then `k` or `k + 1` is a median of `X`; and
`Pr[X > E[X] − 1] ≥ 1/2`, `Pr[X < E[X] + 1] ≥ 1/2`. -/
theorem theorem_4_2 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (l : ℕ) (X : Fin l → Ω → ℝ) (hmeas : ∀ i, Measurable (X i))
    (hbern : ∀ i, ∀ᵐ ω ∂P, X i ω = 0 ∨ X i ω = 1) (hindep : ProbabilityTheory.iIndepFun X P) :
    (∀ k : ℤ, (k : ℝ) ≤ ∫ ω, ∑ i, X i ω ∂P → ∫ ω, ∑ i, X i ω ∂P ≤ (k : ℝ) + 1 →
      ∃ M : ℤ, (M = k ∨ M = k + 1) ∧
        (1 / 2 : ENNReal) ≤ P {ω | ∑ i, X i ω ≤ (M : ℝ)} ∧
        (1 / 2 : ENNReal) ≤ P {ω | (M : ℝ) ≤ ∑ i, X i ω}) ∧
    (1 / 2 : ENNReal) ≤ P {ω | (∫ ω', ∑ i, X i ω' ∂P) - 1 < ∑ i, X i ω} ∧
    (1 / 2 : ENNReal) ≤ P {ω | ∑ i, X i ω < (∫ ω', ∑ i, X i ω' ∂P) + 1} := by sorry

end StratifyMarkets.DoubleAuction
