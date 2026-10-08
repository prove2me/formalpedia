-- Prove2me | Theorems.Thm_QueueingFundamentals_Foundations_poisson_count_cdf
-- name    : QueueingFundamentals.Foundations.poisson_count_cdf
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-03T06:49:53.366976+00:00
-- url     : https://prove2.me/theorems/dc738ddb-166f-49a9-a015-97ece5bcf4d3
-- title:
--   Eq. (1.15) — exponential interarrival times give a Poisson number of arrivals
-- statement:
--   Let $T_0,T_1,\dots$ be independent exponential interarrival times with rate $\lambda>0$, and let $N(t)$ be the number of arrivals in $[0,t]$. Then for every $n\ge0$ and every $t\ge0$ the distribution function $P_n(t)=\Pr\{N(t)\le n\}$ satisfies
--   $$P_n(t)=\int_t^\infty\frac{\lambda(\lambda x)^n}{n!}e^{-\lambda x}\,dx=\sum_{i=0}^{n}\frac{(\lambda t)^i e^{-\lambda t}}{i!},$$
--   and consequently
--   $$\Pr\{N(t)=n\}=\frac{(\lambda t)^n}{n!}e^{-\lambda t}.$$
--
--   The integral is the tail of the Erlang (gamma) distribution of the sum of $n+1$ interarrival times, Eq. (1.15); the sum is the Poisson distribution function. This is the converse of the derivation of the exponential interarrival law from the Poisson process.
-- source:
--   Gross, Shortle, Thompson & Harris, Fundamentals of Queueing Theory, 4th ed., Wiley 2008, DOI 10.1002/9781118625651, pp.18–19, Eq. (1.15) and the Poisson CDF following it

import Mathlib
import Definitions.Def_QueueingFundamentals_Foundations_ArrivalProcess

open MeasureTheory ProbabilityTheory

namespace QueueingFundamentals.Foundations

/-- Eq. (1.15) and the Poisson CDF (pp.18–19): with independent `Exp(λ)` interarrival times, the
number of arrivals `N(t)` by time `t ≥ 0` satisfies
`P_n(t) = Pr{N(t) ≤ n} = ∫_t^∞ λ(λx)^n e^{-λx}/n! dx = ∑_{i=0}^n (λt)^i e^{-λt}/i!`,
and hence `Pr{N(t) = n} = (λt)^n e^{-λt}/n!`. -/
theorem poisson_count_cdf {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (lam : ℝ) (hlam : 0 < lam) (T : ℕ → Ω → ℝ)
    (hT : IsExpInterarrivals μ lam T) (n : ℕ) (t : ℝ) (ht : 0 ≤ t) :
    (μ {ω | countingProcess T t ω ≤ n}).toReal =
        ∫ x in Set.Ioi t, lam * (lam * x) ^ n / (n.factorial : ℝ) * Real.exp (-(lam * x)) ∧
      (μ {ω | countingProcess T t ω ≤ n}).toReal =
        ∑ i ∈ Finset.range (n + 1), (lam * t) ^ i * Real.exp (-(lam * t)) / (i.factorial : ℝ) ∧
      (μ {ω | countingProcess T t ω = n}).toReal =
        (lam * t) ^ n / (n.factorial : ℝ) * Real.exp (-(lam * t)) := by sorry

end QueueingFundamentals.Foundations
