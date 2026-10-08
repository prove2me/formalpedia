-- Prove2me | Theorems.Thm_QueueingFundamentals_GM1_waiting_time_cdf
-- name    : QueueingFundamentals.GM1.waiting_time_cdf
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-03T10:03:55.172995+00:00
-- url     : https://prove2.me/theorems/665860ec-2fd0-4d3b-be69-8c677ac8df65
-- title:
--   Eq. (5.62) — $W_q(t) = 1 - r_0 e^{-\mu(1-r_0)t}$ and $W(t) = 1 - e^{-\mu(1-r_0)t}$
-- statement:
--   Consider the G/M/1 queue with interarrival law $A$ on $[0,\infty)$ of mean $1/\lambda$ ($\lambda>0$), exponential service at rate $\mu>0$, first-come first-served discipline, and $\lambda/\mu < 1$. Let $r_0 \in (0,1)$ be the root of $z = \beta(z)$ and $q$ a stationary arrival-point probability vector. Then for every $t \ge 0$ the line-delay and system-waiting-time CDFs seen by arrivals (defined from $q$ as in §2.2.5) are
--   $$
--   W_q(t) = 1 - r_0 e^{-\mu(1-r_0)t}, \qquad W(t) = 1 - e^{-\mu(1-r_0)t} .
--   $$
--
--   These are the M/M/1 formulas (2.28)–(2.29) with $\rho$ replaced by $r_0$; they describe the waits observed by arriving customers, not the virtual waiting time.
-- source:
--   Gross, Shortle, Thompson & Harris, Fundamentals of Queueing Theory, 4th ed., Wiley 2008, DOI 10.1002/9781118625651, p.263, Eq. (5.62)

import Mathlib
import Definitions.Def_QueueingFundamentals_GM1_EmbeddedChain
import Definitions.Def_QueueingFundamentals_GM1_WaitingTime

namespace QueueingFundamentals.GM1

open MeasureTheory

/-- Eq. (5.62): the FCFS line-delay and system-waiting-time CDFs seen by arrivals are
`W_q(t) = 1 - r_0 e^{-μ(1-r_0)t}` and `W(t) = 1 - e^{-μ(1-r_0)t}` for `t ≥ 0`. -/
theorem waiting_time_cdf (A : Measure ℝ) (lam mu : ℝ) (hlam : 0 < lam) (hmu : 0 < mu)
    (hA : IsInterarrivalLaw A lam) (hrho : lam / mu < 1)
    (r0 : ℝ) (hr0 : r0 ∈ Set.Ioo (0 : ℝ) 1) (hroot : beta A mu (r0 : ℂ) = (r0 : ℂ))
    (q : ℕ → ℝ) (hq : IsArrivalPointStationary A mu q) (t : ℝ) (ht : 0 ≤ t) :
    lineDelayCDF q mu t = 1 - r0 * Real.exp (-mu * (1 - r0) * t) ∧
      systemWaitCDF q mu t = 1 - Real.exp (-mu * (1 - r0) * t) := by sorry

end QueueingFundamentals.GM1
