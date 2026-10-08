-- Prove2me | Theorems.Thm_WhittEfficiency_IS_prop_2_4_increment_law
-- name    : WhittEfficiency.IS.prop_2_4_increment_law
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:53:27.212544+00:00
-- url     : https://prove2.me/theorems/6d76bdcc-4e41-4d97-9e5f-dbca23966b8f
-- title:
--   Proof of Proposition 2.4, p. 712 — A(t) − A(t − 1) has the same distribution as A(1)
-- statement:
--   Let the arrival process be Poisson with rate $\lambda > 0$, i.e. the interarrival times $T_0, T_1, \dots$ are i.i.d. exponential with rate $\lambda$, and let $A(t)$ be the number of arrivals in $(0, t]$. For every $t \ge 1$ the increment $A(t) - A(t-1)$ has the same distribution as $A(1)$:
--
--   $$P\big(A(t) = A(t-1) + k\big) = P\big(A(1) = k\big) \qquad \text{for every } k = 0, 1, 2, \dots$$
--
--   This is the stationary-increment property of the Poisson process over a window of length one, the fact the proof of Proposition 2.4 combines with Proposition 2.3.
--
--   **Formalization Note** The Poisson process is built from exponential interarrival times (`IsExpInterarrivals`), not postulated through its increments, so the statement has content. The event $\{A(t) - A(t-1) = k\}$ is written as $\{A(t) = A(t-1) + k\}$ to avoid natural-number subtraction.
-- source:
--   Whitt, Understanding the efficiency of multi-server service systems, Management Sci. 38 (1992), p. 712, proof of Proposition 2.4

import Mathlib
import Definitions.Def_WhittEfficiency_IS_Model

open MeasureTheory ProbabilityTheory QueueingFundamentals.Foundations

namespace WhittEfficiency.IS

/-- Whitt 1992, proof of Proposition 2.4, p. 712: for a Poisson arrival process of rate `lam`
(i.i.d. exponential interarrival times) and `t ≥ 1`, the increment `A(t) − A(t − 1)` has the same
distribution as `A(1)`. Stated additively to avoid truncated subtraction. -/
theorem prop_2_4_increment_law {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (lam : ℝ) (hlam : 0 < lam) (T : ℕ → Ω → ℝ)
    (hT : IsExpInterarrivals μ lam T) (t : ℝ) (ht : 1 ≤ t) :
    ∀ k : ℕ, μ.real {ω | countingProcess T t ω = countingProcess T (t - 1) ω + k} =
      μ.real {ω | countingProcess T 1 ω = k} := by sorry

end WhittEfficiency.IS
