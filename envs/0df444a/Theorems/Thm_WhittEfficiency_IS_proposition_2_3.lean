-- Prove2me | Theorems.Thm_WhittEfficiency_IS_proposition_2_3
-- name    : WhittEfficiency.IS.proposition_2_3
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T17:53:13.374701+00:00
-- url     : https://prove2.me/theorems/6bd166b3-4516-4596-a718-6cee2c32fe9c
-- title:
--   Proposition 2.3, p. 712 — with all service times 1 in an IS model, N(t) = A(t) − A(t − 1)
-- statement:
--   Consider an infinite-server model in which every customer has service time exactly $1$. Let $A(t)$ be the number of arrivals in $(0, t]$ and $N(t)$ the number of busy servers at time $t$, where an arrival at time $t$ is counted and a departure at time $t$ is not. Then, for every realization of the arrival epochs with only finitely many arrivals in $(0,t]$,
--
--   $$N(t) = A(t) - A(t-1).$$
--
--   The statement is pathwise and holds for any arrival process: a customer arriving at or before $t-1$ has left by time $t$, and every customer arriving in $(t-1, t]$ is still present. It reduces the busy-server count of the M/D/∞ model to an increment of the arrival counting process.
--
--   **Formalization Note** The arrival epochs are $\tau_n = T_0 + \cdots + T_{n-1}$ with all $T_i > 0$, so $A(t)$ (`countingProcess`, which counts $n \ge 1$ with $\tau_n \le t$) is the number of arrivals in $(0,t]$. The hypothesis that only finitely many epochs lie in $(0,t]$ is added because the counts are `Set.ncard`, which returns $0$ on an infinite set; it holds almost surely for Poisson arrivals. The identity is stated in $\mathbb Z$ to avoid truncated natural-number subtraction.
-- source:
--   Whitt, Understanding the efficiency of multi-server service systems, Management Sci. 38 (1992), p. 712, Proposition 2.3 and its proof

import Mathlib
import Definitions.Def_WhittEfficiency_IS_Model

open MeasureTheory ProbabilityTheory QueueingFundamentals.Foundations

namespace WhittEfficiency.IS

/-- Whitt 1992, Proposition 2.3, p. 712: if all service times are `1` in an IS model, then
`N(t) = A(t) − A(t − 1)`, where `A(t)` counts the arrivals in `(0, t]`. Pathwise; the arrival
epochs are positive (`hpos`) and only finitely many arrive by `t` (`hfin`, which makes the counts
genuine cardinalities rather than the junk value of `Set.ncard` on an infinite set). -/
theorem proposition_2_3 {Ω : Type*} (T : ℕ → Ω → ℝ) (ω : Ω) (t : ℝ)
    (hpos : ∀ i, 0 < T i ω)
    (hfin : {n : ℕ | 1 ≤ n ∧ arrivalTime T n ω ≤ t}.Finite) :
    (busyCount T (fun _ _ => 1) t ω : ℤ) = countingProcess T t ω - countingProcess T (t - 1) ω := by sorry

end WhittEfficiency.IS
