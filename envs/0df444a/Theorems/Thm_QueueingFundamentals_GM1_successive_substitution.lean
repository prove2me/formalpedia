-- Prove2me | Theorems.Thm_QueueingFundamentals_GM1_successive_substitution
-- name    : QueueingFundamentals.GM1.successive_substitution
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-03T10:03:22.163973+00:00
-- url     : https://prove2.me/theorems/64162d15-2d7a-4eae-b4b2-7660da348499
-- title:
--   Eq. (5.59) — successive substitution converges to $r_0$
-- statement:
--   Consider the G/M/1 queue with interarrival law $A$ on $[0,\infty)$ of mean $1/\lambda$ ($\lambda>0$) and exponential service at rate $\mu>0$, with $\lambda/\mu < 1$, and let $r_0 \in (0,1)$ be the root of $z = \beta(z)$. For every starting point $0 < z^{(0)} < 1$, the iterates
--   $$
--   z^{(k+1)} = \beta(z^{(k)}) \qquad (k = 0, 1, 2, \dots)
--   $$
--   converge to $r_0$.
--
--   This is the numerical procedure the book recommends for computing $r_0$.
--
--   **Formalization Note** On real arguments the iteration map is $x \mapsto \operatorname{Re}\beta(x)$, which equals $\beta(x)$ since the $b_n$ are real. The root $r_0$ is a hypothesis; it exists and is unique by the preceding milestone.
-- source:
--   Gross, Shortle, Thompson & Harris, Fundamentals of Queueing Theory, 4th ed., Wiley 2008, DOI 10.1002/9781118625651, p.262, Eq. (5.59)

import Mathlib
import Definitions.Def_QueueingFundamentals_GM1_EmbeddedChain

namespace QueueingFundamentals.GM1

open MeasureTheory Filter Topology

/-- Eq. (5.59): when `λ/μ < 1`, successive substitution `z^{(k+1)} = β(z^{(k)})` started at any
`0 < z^{(0)} < 1` converges to the root `r_0 ∈ (0, 1)` of `z = β(z)`. -/
theorem successive_substitution (A : Measure ℝ) (lam mu : ℝ) (hlam : 0 < lam) (hmu : 0 < mu)
    (hA : IsInterarrivalLaw A lam) (hrho : lam / mu < 1)
    (r0 : ℝ) (hr0 : r0 ∈ Set.Ioo (0 : ℝ) 1) (hroot : beta A mu (r0 : ℂ) = (r0 : ℂ))
    (z0 : ℝ) (hz0 : z0 ∈ Set.Ioo (0 : ℝ) 1) :
    Tendsto (fun k : ℕ => (fun x : ℝ => (beta A mu (x : ℂ)).re)^[k] z0) atTop (𝓝 r0) := by sorry

end QueueingFundamentals.GM1
