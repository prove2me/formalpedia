-- Prove2me | Theorems.Thm_QueueingFundamentals_GM1_unique_root_unit_disk
-- name    : QueueingFundamentals.GM1.unique_root_unit_disk
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-03T10:03:22.150991+00:00
-- url     : https://prove2.me/theorems/89edde29-8461-4b32-9434-0acd379657c8
-- title:
--   p.262 — $r_0$ is the only root of $z = \beta(z)$ in the open unit disk
-- statement:
--   Consider the G/M/1 queue with interarrival law $A$ on $[0,\infty)$ of mean $1/\lambda$ ($\lambda>0$) and exponential service at rate $\mu>0$, and let $\beta(z) = \sum_n b_n z^n$ as in (5.55). If $\lambda/\mu < 1$, then there is exactly one complex number $z$ with
--   $$
--   |z| < 1 \quad\text{and}\quad z = \beta(z).
--   $$
--
--   Together with the real root $r_0 \in (0,1)$, this shows that $r_0$ is the only root of the characteristic equation inside the unit disk, which is why the stationary vector is a single geometric term.
-- source:
--   Gross, Shortle, Thompson & Harris, Fundamentals of Queueing Theory, 4th ed., Wiley 2008, DOI 10.1002/9781118625651, p.262, the argument by Rouché's theorem following Figure 5.2

import Mathlib
import Definitions.Def_QueueingFundamentals_GM1_EmbeddedChain

namespace QueueingFundamentals.GM1

open MeasureTheory

/-- p.262 (Rouché's theorem): when `λ/μ < 1` there is exactly one complex root of `z = β(z)` with
`|z| < 1`. -/
theorem unique_root_unit_disk (A : Measure ℝ) (lam mu : ℝ) (hlam : 0 < lam) (hmu : 0 < mu)
    (hA : IsInterarrivalLaw A lam) (hrho : lam / mu < 1) :
    ∃! z : ℂ, ‖z‖ < 1 ∧ beta A mu z = z := by sorry

end QueueingFundamentals.GM1
