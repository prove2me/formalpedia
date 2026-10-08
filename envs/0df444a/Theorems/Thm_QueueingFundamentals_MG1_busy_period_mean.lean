-- Prove2me | Theorems.Thm_QueueingFundamentals_MG1_busy_period_mean
-- name    : QueueingFundamentals.MG1.busy_period_mean
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-03T09:39:38.713791+00:00
-- url     : https://prove2.me/theorems/9984fc5e-c986-4be1-9b89-a77f282c5c73
-- title:
--   §5.1.6 — the mean M/G/1 busy period is 1/(μ − λ)
-- statement:
--   Let $\lambda > 0$, let $B$ be a service-time distribution on $[0,\infty)$ with finite mean $\mathrm E[S] > 0$, put $\mu = 1/\mathrm E[S]$ and assume $\rho = \lambda/\mu < 1$. If $G$ is a probability distribution on $[0,\infty)$ satisfying the busy-period equation (5.36), then $G$ has a finite mean and
--
--   $$
--   \mathrm E[X] = \int_0^\infty x\,dG(x) = \frac{1/\mu}{1 - \lambda/\mu} = \frac{1}{\mu - \lambda}.
--   $$
--
--   The mean busy period depends on the service distribution only through its mean, and agrees with the M/M/1 value.
--
--   **Formalization Note** $\mathrm E[S] > 0$ is assumed so that $\mu = 1/\mathrm E[S]$ is the book's service rate (in Lean `1/0 = 0`). The conclusion states the integrability of $x$ under $G$ as well as the value.
-- source:
--   Gross, Shortle, Thompson & Harris, Fundamentals of Queueing Theory, 4th ed., Wiley 2008, DOI 10.1002/9781118625651, p.240, mean length of the busy period, §5.1.6

import Mathlib
import Definitions.Def_QueueingFundamentals_MG1_embeddedChain
import Definitions.Def_QueueingFundamentals_MG1_transforms

namespace QueueingFundamentals.MG1

open MeasureTheory

/-- The mean busy period, p.240: if `0 < E[S] < ∞`, `μ = 1/E[S]`, `ρ = λ/μ < 1`, and the
busy-period distribution `G` (a probability distribution on `[0, ∞)`) satisfies (5.36), then
`G` has finite mean `E[X] = (1/μ)/(1 - λ/μ) = 1/(μ - λ)`. -/
theorem busy_period_mean (lam : ℝ) (hlam : 0 < lam) (B : Measure ℝ) [IsProbabilityMeasure B]
    (hB : B (Set.Iio 0) = 0)
    (hint : Integrable (fun t : ℝ => t) B) (hmean : 0 < meanService B)
    (hρ : utilization lam B < 1)
    (G : Measure ℝ) [IsProbabilityMeasure G] (hG : G (Set.Iio 0) = 0)
    (hGeq : IsBusyPeriodEquation lam B G) :
    Integrable (fun x : ℝ => x) G ∧
      ∫ x, x ∂G = 1 / ((meanService B)⁻¹ - lam) := by sorry

end QueueingFundamentals.MG1
