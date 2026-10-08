-- Prove2me | Theorems.Thm_QueueingFundamentals_GM1_unique_root_unit_interval
-- name    : QueueingFundamentals.GM1.unique_root_unit_interval
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-03T10:03:07.268169+00:00
-- url     : https://prove2.me/theorems/a1ac2b3a-65b5-4f38-8489-d5f64cf0630b
-- title:
--   pp.261–262 — $z = \beta(z)$ has exactly one root in $(0,1)$ iff $\lambda/\mu < 1$
-- statement:
--   Consider the G/M/1 queue with interarrival law $A$ on $[0,\infty)$ of mean $1/\lambda$ ($\lambda>0$) and exponential service at rate $\mu > 0$, and let $\beta(z) = \sum_n b_n z^n$ be the generating function (5.55). Then:
--
--   1. the equation $z = \beta(z)$ has at most one real root in $(0,1)$;
--   2. it has a root in $(0,1)$ if and only if
--   $$
--   \frac{\lambda}{\mu} < 1 .
--   $$
--
--   This is the book's comparison of the graphs $y = \beta(z)$ and $y = z$ (5.58), Figure 5.2: either there is no intersection in $(0,1)$, or exactly one, and the latter case occurs when $\beta'(1) = \mu/\lambda > 1$. The root is denoted $r_0$.
-- source:
--   Gross, Shortle, Thompson & Harris, Fundamentals of Queueing Theory, 4th ed., Wiley 2008, DOI 10.1002/9781118625651, pp.261–262, Eq. (5.58) and Figure 5.2 ("there is exactly one root r_0 of (5.55) in (0, 1)")

import Mathlib
import Definitions.Def_QueueingFundamentals_GM1_EmbeddedChain

namespace QueueingFundamentals.GM1

open MeasureTheory

/-- pp.261–262, the graphs of (5.58): `z = β(z)` has at most one root in `(0, 1)`, and it has one
exactly when `λ/μ < 1`. -/
theorem unique_root_unit_interval (A : Measure ℝ) (lam mu : ℝ) (hlam : 0 < lam) (hmu : 0 < mu)
    (hA : IsInterarrivalLaw A lam) :
    (∀ r s : ℝ, r ∈ Set.Ioo (0 : ℝ) 1 → beta A mu (r : ℂ) = (r : ℂ) →
        s ∈ Set.Ioo (0 : ℝ) 1 → beta A mu (s : ℂ) = (s : ℂ) → r = s) ∧
      ((∃ r : ℝ, r ∈ Set.Ioo (0 : ℝ) 1 ∧ beta A mu (r : ℂ) = (r : ℂ)) ↔ lam / mu < 1) := by sorry

end QueueingFundamentals.GM1
