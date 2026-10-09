-- Prove2me | Theorems.Thm_RFRidge_Basic_proposition_1
-- name    : RFRidge.Basic.proposition_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T00:48:02.03329+00:00
-- url     : https://prove2.me/theorems/1b799ca8-10e4-4ce7-8cf5-8a31fb9294cd
-- title:
--   Proposition 1 (Bernstein, random variables), p. 36 — (1/n)Σxᵢ ≤ 2T log(1/δ)/(3n) + √(2S log(1/δ)/n) w.p. ≥ 1 − δ
-- statement:
--   Let $x_1,\dots,x_n$ ($n\ge1$) be independent, identically distributed real random variables with zero mean, such that $x_i\le T$ almost surely and $\mathbb E x_i^2\le S$. Then for every $\delta>0$:
--
--   1. with probability at least $1-\delta$,
--   $$\frac1n\sum_{i=1}^nx_i\le\frac{2T\log\frac1\delta}{3n}+\sqrt{\frac{2S\log\frac1\delta}{n}};$$
--   2. if moreover $|x_i|\le T'$ almost surely for all $i$, then with probability at least $1-2\delta$ the same bound with $T'$ in place of $T$ holds for $\big|\frac1n\sum_{i=1}^nx_i\big|$.
--
--   This scalar Bernstein inequality is used to concentrate the empirical effective dimension (Lemma 10).
--
--   **Formalization Note** Each claim is stated as "the failure event has probability at most $\delta$ (resp. $2\delta$)". The variables are on a common probability space, measurable, mutually independent, identically distributed and square integrable (which makes $\mathbb E x_i^2$ a genuine integral). $n\ge1$ is added for $1/n$. For $\delta>1$ both claims hold trivially, so the page's "$\delta>0$" is kept.
-- source:
--   Rudi & Rosasco, arXiv:1602.04474v5, Proposition 1, p. 36

import Mathlib

namespace RFRidge.Basic

open MeasureTheory ProbabilityTheory

/-- Proposition 1 (Bernstein's inequality for sums of random variables), p. 36. Let `x₀, …, x_{n−1}` be
i.i.d. real random variables with zero mean, `xᵢ ≤ T` almost surely and `E xᵢ² ≤ S`. For every `δ > 0`:
(1) with probability at least `1 − δ`, `(1/n) Σᵢ xᵢ ≤ 2T log(1/δ)/(3n) + √(2S log(1/δ)/n)`;
(2) if moreover `|xᵢ| ≤ T'` almost surely, then with probability at least `1 − 2δ`,
`|(1/n) Σᵢ xᵢ| ≤ 2T' log(1/δ)/(3n) + √(2S log(1/δ)/n)`.
Each is stated as a bound on the probability of the failure event. -/
theorem proposition_1 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (n : ℕ) (hn : 1 ≤ n) (x : Fin n → Ω → ℝ)
    (hmeas : ∀ i, Measurable (x i)) (hind : iIndepFun x P)
    (hid : ∀ i, IdentDistrib (x i) (x ⟨0, hn⟩) P P)
    (hL2 : ∀ i, MemLp (x i) 2 P) (hmean : ∀ i, ∫ ω, x i ω ∂P = 0)
    (T S : ℝ) (hT : ∀ i, ∀ᵐ ω ∂P, x i ω ≤ T) (hS : ∀ i, ∫ ω, x i ω ^ 2 ∂P ≤ S)
    (δ : ℝ) (hδ : 0 < δ) :
    P {ω | 2 * T * Real.log (1 / δ) / (3 * n) + Real.sqrt (2 * S * Real.log (1 / δ) / n)
          < (1 / (n : ℝ)) * ∑ i, x i ω} ≤ ENNReal.ofReal δ ∧
    ∀ T' : ℝ, (∀ i, ∀ᵐ ω ∂P, |x i ω| ≤ T') →
      P {ω | 2 * T' * Real.log (1 / δ) / (3 * n) + Real.sqrt (2 * S * Real.log (1 / δ) / n)
            < |(1 / (n : ℝ)) * ∑ i, x i ω|} ≤ ENNReal.ofReal (2 * δ) := by sorry

end RFRidge.Basic
