-- Prove2me | Theorems.Thm_WhittEfficiency_IS_proposition_2_4
-- name    : WhittEfficiency.IS.proposition_2_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:53:30.136736+00:00
-- url     : https://prove2.me/theorems/e748b8dc-6d49-4652-b1c1-d53d97dd80fd
-- title:
--   Proposition 2.4, p. 712 — in M/D/∞ with unit service times, N(t) ~ Poisson(λ) for each t > 1
-- statement:
--   Consider the M/D/∞ model: Poisson arrivals with rate $\lambda > 0$ (i.i.d. exponential interarrival times), infinitely many servers, and every service time equal to $1$, the system starting empty at time $0$. Let $N(t)$ be the number of busy servers at time $t$. Then for each $t > 1$, $N(t)$ has a Poisson distribution with mean $\lambda$:
--
--   $$P\big(N(t) = k\big) = e^{-\lambda}\,\frac{\lambda^k}{k!}, \qquad k = 0, 1, 2, \dots$$
--
--   The mean and the variance of $N(t)$ are both $\lambda$, which is the starting point of the paper's derivation of the square-root staffing formula $s = \lambda + \gamma\sqrt{\lambda}$.
--
--   **Formalization Note** The Poisson law is stated pointwise through the probability mass function. The printed condition $t > 1$ is kept as is.
-- source:
--   Whitt, Understanding the efficiency of multi-server service systems, Management Sci. 38 (1992), p. 712, Proposition 2.4

import Mathlib
import Definitions.Def_WhittEfficiency_IS_Model

open MeasureTheory ProbabilityTheory QueueingFundamentals.Foundations

namespace WhittEfficiency.IS

/-- Whitt 1992, Proposition 2.4, p. 712: in an M/D/∞ model with service times of length `1` and
Poisson arrivals of rate `lam`, the number of busy servers `N(t)` is Poisson with mean `lam` for
each `t > 1`. -/
theorem proposition_2_4 {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (lam : ℝ) (hlam : 0 < lam) (T : ℕ → Ω → ℝ)
    (hT : IsExpInterarrivals μ lam T) (t : ℝ) (ht : 1 < t) :
    ∀ k : ℕ, μ.real {ω | busyCount T (fun _ _ => 1) t ω = k} =
      Real.exp (-lam) * lam ^ k / k.factorial := by sorry

end WhittEfficiency.IS
