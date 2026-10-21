-- Prove2me | Theorems.Thm_StochLoadBal_Makespan_lemma_4
-- name    : StochLoadBal.Makespan.lemma_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T09:18:09.921893+00:00
-- url     : https://prove2.me/theorems/3e3eaa77-1cef-472a-914b-38b629af4ac8
-- title:
--   Lemma 4 — truncated items lower bound: Σ_j β_m(X_j) ≥ 17m forces expected makespan ≥ c₁
-- statement:
--   There is an absolute constant $c_1>0$ with the following property. Let $m\ge1$, let $X_1,\dots,X_n$ be independent random variables with values in $[0,1]$, and let $\{J_i\}_{i=1}^m$ be any partition of $[n]$ (given by an assignment $\sigma:[n]\to[m]$, $J_i=\sigma^{-1}(i)$). If
--   $$\sum_{j=1}^n \beta_m(X_j)\ \ge\ 17\,m,$$
--   then
--   $$\mathbb E\Big[\max_{i\in[m]}\sum_{j\in J_i}X_j\Big]\ \ge\ c_1 .$$
--
--   Here $\beta_m$ is the effective size of Definition 1 (with $\beta_1=\mathbb E$). Lemma 4 is the lower bound for truncated parts; applied to the machines of a subset $K$ with $k=|K|$, it yields the constraints (4) and (8) on every subset of machines.
--
--   **Formalization Note** The page's conclusion "$=\Omega(1)$" is written as an explicit constant $c_1>0$ quantified before everything else, so it does not depend on $m$, $n$ or the distributions. The machines are identical here (job $j$ has size $X_j$ on every machine).
-- source:
--   Gupta, Kumar, Nagarajan & Shen, Stochastic Load Balancing on Unrelated Machines, arXiv:1904.07271v1, p. 7, Lemma 4 (proof pp. 7–8)

import Mathlib
import Definitions.Def_StochLoadBal_Makespan_Model

namespace StochLoadBal.Makespan

open MeasureTheory ProbabilityTheory

/-- Lemma 4 (Truncated Items Lower Bound, p. 7), with the `Ω(1)` made an absolute constant `c₁`:
for independent `[0, 1]`-valued `X_1, …, X_n` and any partition `{J_i}` of the jobs among `m`
machines (here `J_i = {j | σ j = i}`), if `Σ_j β_m(X_j) ≥ 17 m` then
`E[max_i Σ_{j ∈ J_i} X_j] ≥ c₁`. -/
theorem lemma_4 :
    ∃ c₁ : ℝ, 0 < c₁ ∧
      ∀ (m n : ℕ), 1 ≤ m →
      ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (X : Fin n → Ω → ℝ),
        (∀ j, Measurable (X j)) → iIndepFun X P →
        (∀ j ω, 0 ≤ X j ω ∧ X j ω ≤ 1) →
        ∀ σ : Fin n → Fin m,
          17 * (m : ℝ) ≤ ∑ j, effSize P m (X j) →
          c₁ ≤ expMakespan P (fun _ : Fin m => X) σ := by sorry

end StochLoadBal.Makespan
