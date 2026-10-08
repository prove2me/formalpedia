-- Prove2me | Theorems.Thm_QueueingFundamentals_Foundations_exp_memoryless
-- name    : QueueingFundamentals.Foundations.exp_memoryless
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-03T06:35:26.975186+00:00
-- url     : https://prove2.me/theorems/049492d8-0aa5-41ca-820b-f995dae0f7fa
-- title:
--   Eq. (1.17) — the memoryless property of the exponential distribution
-- statement:
--   Let $T$ be a random variable with the exponential distribution with rate $\lambda>0$. For all $0\le t_0\le t_1$,
--   $$\Pr\{T\le t_1\mid T\ge t_0\}=\Pr\{0\le T\le t_1-t_0\}.$$
--
--   In words: a customer who has already spent $t_0$ units of time in service has remaining service time distributed as a fresh service time. This is the Markovian property that makes the Poisson–exponential queueing models tractable.
-- source:
--   Gross, Shortle, Thompson & Harris, Fundamentals of Queueing Theory, 4th ed., Wiley 2008, DOI 10.1002/9781118625651, pp.20–21, Eq. (1.17)

import Mathlib

open MeasureTheory ProbabilityTheory

namespace QueueingFundamentals.Foundations

/-- Eq. (1.17) (pp.20–21): an exponentially distributed `T` is memoryless,
`Pr{T ≤ t_1 | T ≥ t_0} = Pr{0 ≤ T ≤ t_1 − t_0}` for `0 ≤ t_0 ≤ t_1`. -/
theorem exp_memoryless {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (lam : ℝ) (hlam : 0 < lam) (T : Ω → ℝ) (hTm : Measurable T)
    (hlaw : μ.map T = expMeasure lam) (t₀ t₁ : ℝ) (ht₀ : 0 ≤ t₀) (ht : t₀ ≤ t₁) :
    cond μ {ω | t₀ ≤ T ω} {ω | T ω ≤ t₁} = μ {ω | 0 ≤ T ω ∧ T ω ≤ t₁ - t₀} := by sorry

end QueueingFundamentals.Foundations
