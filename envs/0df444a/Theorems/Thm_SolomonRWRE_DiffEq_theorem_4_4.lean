-- Prove2me | Theorems.Thm_SolomonRWRE_DiffEq_theorem_4_4
-- name    : SolomonRWRE.DiffEq.theorem_4_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T15:30:58.3469+00:00
-- url     : https://prove2.me/theorems/9a10e694-36c5-4ceb-ac93-f2b6aa323de9
-- title:
--   Theorem (4.4) — (Z_1 + ⋯ + Z_n)/n → ν/(1 − ν) a.e. if ν = E(σ) < 1, and → ∞ a.e. if ν ≥ 1
-- statement:
--   Let $\sigma_1,\sigma_2,\dots$ be independent, identically distributed, nonnegative random variables, and let $Z_n$ solve the system of difference equations (4.1):
--   $$
--   Z_0=0,\qquad Z_n=\sigma_n(1+Z_{n-1}),\quad n\ge1 .
--   $$
--   Let $\nu=E(\sigma)\in[0,\infty]$. Then almost surely
--   $$
--   \lim_{n\to\infty}\frac{Z_1+\dots+Z_n}{n}=\begin{cases}\dfrac{\nu}{1-\nu}, & \nu<1,\\[2mm] \infty, & \nu\ge1.\end{cases}
--   $$
--
--   For the random walk in a random environment, $2Z_n+1$ is the conditional mean first-passage time from $n$ to $n+1$ given the environment (with $0$ reflecting). The theorem therefore gives the growth rate of the mean time to reach level $n$ in a typical environment.
--
--   **Formalization Note** $\nu$ is a lower Lebesgue integral in $[0,\infty]$; $\sigma$ need not be integrable, and $\nu=\infty$ falls in the second case. The averages are taken in $[0,\infty]$, which loses nothing since $Z_k\ge0$. Both cases are almost-sure limits.
-- source:
--   Solomon, Random Walks in a Random Environment, Ann. Probab. 3(1):1–31 (1975), DOI 10.1214/aop/1176996444, p. 28, Theorem (4.4)

import Mathlib
import Definitions.Def_SolomonRWRE_DiffEq_System

open MeasureTheory ProbabilityTheory Filter Topology

namespace SolomonRWRE.DiffEq

/-- **Theorem (4.4)** (Solomon, Random Walks in a Random Environment, Ann. Probab. 3(1)
(1975), p. 28). Let `ν = E(σ)`. Then a.e.
`lim_{n→∞} (Z_1 + ⋯ + Z_n)/n = ν/(1 − ν)` if `ν < 1`, and `= ∞` if `ν ≥ 1`.

**Formalization Note.** `Z` solves (4.1) with `σ_1, σ_2, …` i.i.d. nonnegative
(`IsIIDNonneg`). `ν` is the lower Lebesgue integral of `σ_1` in `[0, ∞]` (`ν = ∞` is
allowed and falls in the second case). The averages are taken in `[0, ∞]` through
`ENNReal.ofReal`, which loses nothing as `Z_k ≥ 0`; both cases are almost-sure limits. -/
theorem theorem_4_4 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (σ : ℕ → Ω → ℝ) (hσ : IsIIDNonneg P σ) :
    (nu P σ < 1 → ∀ᵐ ω ∂P,
      Tendsto (fun n : ℕ => ENNReal.ofReal ((∑ k ∈ Finset.Icc 1 n, Z σ k ω) / n)) atTop
        (𝓝 (nu P σ / (1 - nu P σ)))) ∧
    (1 ≤ nu P σ → ∀ᵐ ω ∂P,
      Tendsto (fun n : ℕ => ENNReal.ofReal ((∑ k ∈ Finset.Icc 1 n, Z σ k ω) / n)) atTop
        (𝓝 ⊤)) := by sorry

end SolomonRWRE.DiffEq
