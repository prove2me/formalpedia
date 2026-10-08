-- Prove2me | Theorems.Thm_QueueingFundamentals_Transient_busy_period_mean
-- name    : QueueingFundamentals.Transient.busy_period_mean
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-03T08:05:36.967525+00:00
-- url     : https://prove2.me/theorems/a0f47bd1-ce31-4e40-a589-fb181bdcf2d7
-- title:
--   Eq. (2.79) — mean busy period $1/(\mu-\lambda)$ and mean busy cycle of M/M/1
-- statement:
--   Let $0 < \lambda < \mu$ and let $f(t) = \sqrt{\mu/\lambda}\,e^{-(\lambda+\mu)t} I_1(2\sqrt{\lambda\mu}\,t)/t$ be the M/M/1 busy-period density. Then $f$ is a probability density on $(0,\infty)$, and the busy period $T_{bp}$ and the busy cycle $T_{bc}$ (an idle period, exponential with rate $\lambda$, followed by an independent busy period, whose density is $g(t) = \int_0^t \lambda e^{-\lambda(t-u)} f(u)\,du$) have means
--
--   $$
--   E[T_{bp}] = \int_0^\infty t f(t)\,dt = \frac{1}{\mu-\lambda}, \qquad
--   E[T_{bc}] = \int_0^\infty t\, g(t)\,dt = \frac{1}{\lambda} + \frac{1}{\mu-\lambda}.
--   $$
--
--   The book derives (2.79) by a steady-state ratio argument that holds for every M/G/1 queue; this statement is its M/M/1 instance, computed from the explicit busy-period density.
--
--   **Formalization Note** Integrability of $f$, $t f(t)$ and $t g(t)$ on $(0,\infty)$ is part of the conclusion.
-- source:
--   Gross, Shortle, Thompson & Harris, Fundamentals of Queueing Theory, 4th ed., Wiley 2008, DOI 10.1002/9781118625651, p.103, Eq. (2.79), §2.12

import Mathlib
import Definitions.Def_QueueingFundamentals_Transient_busyPeriodDensity

namespace QueueingFundamentals.Transient

open MeasureTheory

/-- (2.79) for the M/M/1 queue (p.103). Let `0 < λ < μ` and let `f` be the busy-period density
of p.102. Then `f` is a probability density on `(0, ∞)`, the busy period has mean
`E[T_bp] = ∫ t f(t) dt = 1/(μ - λ)`, and the busy cycle — an exponential idle period of rate `λ`
followed by an independent busy period, with density
`g(t) = ∫_0^t λ e^{-λ(t-u)} f(u) du` — has mean `E[T_bc] = 1/λ + 1/(μ - λ)`. -/
theorem busy_period_mean (lam mu : ℝ) (hlam : 0 < lam) (hlt : lam < mu) :
    IntegrableOn (busyPeriodDensity lam mu) (Set.Ioi 0) ∧
      ∫ t in Set.Ioi (0 : ℝ), busyPeriodDensity lam mu t = 1 ∧
      IntegrableOn (fun t : ℝ => t * busyPeriodDensity lam mu t) (Set.Ioi 0) ∧
      ∫ t in Set.Ioi (0 : ℝ), t * busyPeriodDensity lam mu t = 1 / (mu - lam) ∧
      IntegrableOn
        (fun t : ℝ => t * ∫ u in (0 : ℝ)..t,
          lam * Real.exp (-lam * (t - u)) * busyPeriodDensity lam mu u) (Set.Ioi 0) ∧
      ∫ t in Set.Ioi (0 : ℝ), t * ∫ u in (0 : ℝ)..t,
          lam * Real.exp (-lam * (t - u)) * busyPeriodDensity lam mu u
        = 1 / lam + 1 / (mu - lam) := by sorry

end QueueingFundamentals.Transient
