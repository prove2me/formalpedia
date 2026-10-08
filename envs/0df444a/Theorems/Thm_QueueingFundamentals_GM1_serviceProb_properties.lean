-- Prove2me | Theorems.Thm_QueueingFundamentals_GM1_serviceProb_properties
-- name    : QueueingFundamentals.GM1.serviceProb_properties
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-03T10:02:57.800008+00:00
-- url     : https://prove2.me/theorems/5372ad70-2e47-44de-9803-9e59d77acd15
-- title:
--   p.261 — $0 < b_0 < 1$, $b_n > 0$, $\beta(1) = 1$, $\beta'(1) = \mu/\lambda$
-- statement:
--   Consider the G/M/1 queue with interarrival law $A$ on $[0,\infty)$ of mean $1/\lambda$ ($\lambda > 0$) and exponential service at rate $\mu > 0$, and let $b_n = \int_0^\infty e^{-\mu t}(\mu t)^n/n!\,dA(t)$ as in (5.50). Then
--
--   1. $0 < \beta(0) = b_0 < 1$;
--   2. $b_n > 0$ for every $n \ge 0$;
--   3. $\beta(1) = \sum_{n\ge0} b_n = 1$;
--   4. $$\beta'(1) = \sum_{n\ge1} n b_n = E[\text{number served during interarrival time}] = \frac{\mu}{\lambda}.$$
--
--   These facts give the shape of $y = \beta(z)$ on $[0,1]$ (Figure 5.2) on which the root argument rests.
--
--   **Formalization Note** $\beta'(1)$ is written as the series $\sum_n n b_n$, the book's formula for $\beta'(z)$ at $z = 1$.
-- source:
--   Gross, Shortle, Thompson & Harris, Fundamentals of Queueing Theory, 4th ed., Wiley 2008, DOI 10.1002/9781118625651, p.261, properties of β(z) following Eq. (5.58)

import Mathlib
import Definitions.Def_QueueingFundamentals_GM1_EmbeddedChain

namespace QueueingFundamentals.GM1

open MeasureTheory

/-- p.261: `0 < β(0) = b_0 < 1`, every `b_n > 0`, `β(1) = ∑ b_n = 1`, and
`β'(1) = ∑ n b_n = E[number served during interarrival time] = μ/λ`. -/
theorem serviceProb_properties (A : Measure ℝ) (lam mu : ℝ) (hlam : 0 < lam) (hmu : 0 < mu)
    (hA : IsInterarrivalLaw A lam) :
    0 < serviceProb A mu 0 ∧ serviceProb A mu 0 < 1 ∧
      (∀ n, 0 < serviceProb A mu n) ∧
      HasSum (fun n : ℕ => serviceProb A mu n) 1 ∧
      HasSum (fun n : ℕ => (n : ℝ) * serviceProb A mu n) (mu / lam) := by sorry

end QueueingFundamentals.GM1
