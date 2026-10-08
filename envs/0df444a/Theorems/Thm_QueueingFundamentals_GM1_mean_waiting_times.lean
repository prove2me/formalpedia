-- Prove2me | Theorems.Thm_QueueingFundamentals_GM1_mean_waiting_times
-- name    : QueueingFundamentals.GM1.mean_waiting_times
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-03T10:03:55.703928+00:00
-- url     : https://prove2.me/theorems/ca584f3a-aed2-40e3-a074-3e9e8eec87ec
-- title:
--   Eq. (5.63) — $W_q = r_0/(\mu(1-r_0))$ and $W = 1/(\mu(1-r_0))$
-- statement:
--   Under the hypotheses of Eq. (5.62) (G/M/1 queue, $\lambda/\mu < 1$, FCFS, $r_0 \in (0,1)$ the root of $z = \beta(z)$, $q$ a stationary arrival-point probability vector), the mean line delay and mean system waiting time are
--   $$
--   W_q = \int_0^\infty [1 - W_q(t)]\,dt = \frac{r_0}{\mu(1 - r_0)}, \qquad W = \int_0^\infty [1 - W(t)]\,dt = \frac{1}{\mu(1 - r_0)} .
--   $$
--
--   **Formalization Note** The means are the integrals of the tail $1 - W_q(t)$ and $1 - W(t)$ over $(0,\infty)$, as in the book's recomputation of $W_q$ on p.65; the statement also asserts that both tails are integrable, so the integrals are not Lean's default value.
-- source:
--   Gross, Shortle, Thompson & Harris, Fundamentals of Queueing Theory, 4th ed., Wiley 2008, DOI 10.1002/9781118625651, p.263, Eq. (5.63)

import Mathlib
import Definitions.Def_QueueingFundamentals_GM1_EmbeddedChain
import Definitions.Def_QueueingFundamentals_GM1_WaitingTime

namespace QueueingFundamentals.GM1

open MeasureTheory

/-- Eq. (5.63): the mean line delay and mean system waiting time seen by arrivals,
`W_q = ∫_0^∞ [1 - W_q(t)] dt = r_0/(μ(1 - r_0))` and `W = ∫_0^∞ [1 - W(t)] dt = 1/(μ(1 - r_0))`. -/
theorem mean_waiting_times (A : Measure ℝ) (lam mu : ℝ) (hlam : 0 < lam) (hmu : 0 < mu)
    (hA : IsInterarrivalLaw A lam) (hrho : lam / mu < 1)
    (r0 : ℝ) (hr0 : r0 ∈ Set.Ioo (0 : ℝ) 1) (hroot : beta A mu (r0 : ℂ) = (r0 : ℂ))
    (q : ℕ → ℝ) (hq : IsArrivalPointStationary A mu q) :
    IntegrableOn (fun t => 1 - lineDelayCDF q mu t) (Set.Ioi 0) ∧
      ∫ t in Set.Ioi (0 : ℝ), (1 - lineDelayCDF q mu t) = r0 / (mu * (1 - r0)) ∧
      IntegrableOn (fun t => 1 - systemWaitCDF q mu t) (Set.Ioi 0) ∧
      ∫ t in Set.Ioi (0 : ℝ), (1 - systemWaitCDF q mu t) = 1 / (mu * (1 - r0)) := by sorry

end QueueingFundamentals.GM1
