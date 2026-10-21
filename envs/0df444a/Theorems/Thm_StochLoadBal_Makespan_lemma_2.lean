-- Prove2me | Theorems.Thm_StochLoadBal_Makespan_lemma_2
-- name    : StochLoadBal.Makespan.lemma_2
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-20T09:18:14.720505+00:00
-- url     : https://prove2.me/theorems/9a72ac4a-9813-4b36-ab98-780299949b92
-- title:
--   Lemma 2 — effective-size Chernoff bound: Σ_i β_k(Y_i) ≤ b implies Pr[Σ_i Y_i ≥ c] ≤ (1/k)^(c−b)
-- statement:
--   Let $k\ge2$ be an integer and let $Y_1,\dots,Y_n$ be independent real random variables with $\mathbb E\big[e^{(\log k)Y_i}\big]<\infty$. If
--   $$\sum_{i=1}^n \beta_k(Y_i)\ \le\ b,$$
--   then for every real $c$,
--   $$\Pr\Big[\sum_{i=1}^n Y_i\ \ge\ c\Big]\ \le\ \Big(\frac1k\Big)^{c-b}.$$
--
--   This is the upper-bound property of effective sizes: a total effective size at most $b$ makes a load above $b+\alpha$ have probability at most $k^{-\alpha}$. It gives the per-machine tail bound of Observation 3.
--
--   **Formalization Note** The lemma is stated for integers $k\ge2$, where Definition 1's formula applies; for $k=1$ the right side is $1$ and the statement is empty. The exponential-moment hypothesis makes $\beta_k(Y_i)$ the logarithm of a finite moment generating function rather than a junk value.
-- source:
--   Gupta, Kumar, Nagarajan & Shen, Stochastic Load Balancing on Unrelated Machines, arXiv:1904.07271v1, p. 6, Lemma 2

import Mathlib
import Definitions.Def_StochLoadBal_Makespan_Model

namespace StochLoadBal.Makespan

open MeasureTheory ProbabilityTheory

/-- Lemma 2 (Upper Bound, p. 6): for an integer `k ≥ 2` and independent random variables
`Y_1, …, Y_n` with finite exponential moments `E[e^{(log k) Y_i}]`, if `Σ_i β_k(Y_i) ≤ b` then
`Pr[Σ_i Y_i ≥ c] ≤ (1/k)^{c - b}` for every real `c`. -/
theorem lemma_2 {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (n : ℕ) (Y : Fin n → Ω → ℝ) (hmeas : ∀ i, Measurable (Y i)) (hind : iIndepFun Y P)
    (k : ℕ) (hk : 2 ≤ k)
    (hint : ∀ i, Integrable (fun ω => Real.exp (Real.log k * Y i ω)) P)
    (b c : ℝ) (hb : ∑ i, effSize P k (Y i) ≤ b) :
    (P {ω | c ≤ ∑ i, Y i ω}).toReal ≤ (1 / (k : ℝ)) ^ (c - b) := by sorry

end StochLoadBal.Makespan
