-- Prove2me | Theorems.Thm_QueueingFundamentals_GM1_arrival_point_geometric
-- name    : QueueingFundamentals.GM1.arrival_point_geometric
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-03T10:03:32.823317+00:00
-- url     : https://prove2.me/theorems/9449bf4a-a14a-43fa-b0c4-1e30d3169a88
-- title:
--   Eq. (5.60) — the G/M/1 arrival-point law is geometric, $q_n = (1-r_0)r_0^n$
-- statement:
--   Consider the G/M/1 queue: interarrival times are independent with law $A$ on $[0,\infty)$ of mean $1/\lambda$ ($\lambda>0$), service times are exponential with rate $\mu > 0$, and $\rho = \lambda/\mu < 1$. Let $b_n$ be the probabilities (5.50), $P$ the arrival-point transition matrix (5.51), and $\beta(z) = \sum_n b_n z^n$ (5.55). Then there is a real number $r_0$ with the following properties:
--
--   1. $0 < r_0 < 1$ and $r_0 = \beta(r_0)$;
--   2. $r_0$ is the only complex root of $z = \beta(z)$ with $|z| < 1$;
--   3. the geometric vector
--   $$
--   q_n = (1 - r_0)\, r_0^{\,n} \qquad (n \ge 0,\ \rho < 1)
--   $$
--   is a probability vector solving $qP = q$, $qe = 1$ (5.52);
--   4. it is the only probability vector solving (5.52).
--
--   So the number of customers an arrival finds in the system is geometric, as in the M/M/1 queue with $\rho$ replaced by $r_0$. This is the arrival-point law $q_n$, not the time-average law $p_n$: the two agree only for Poisson input.
--
--   **Formalization Note** The root $r_0$ is not a hypothesis: its existence, its location in $(0,1)$, and its uniqueness in the unit disk are part of the conclusion, and so is the uniqueness of the stationary vector, which the book's phrase "the steady-state arrival-point distribution is" asserts.
-- source:
--   Gross, Shortle, Thompson & Harris, Fundamentals of Queueing Theory, 4th ed., Wiley 2008, DOI 10.1002/9781118625651, p.262, Eq. (5.60), with the root results of pp.261–262

import Mathlib
import Definitions.Def_QueueingFundamentals_GM1_EmbeddedChain

namespace QueueingFundamentals.GM1

open MeasureTheory

/-- Eq. (5.60) with the root result of pp.261–262: when `ρ = λ/μ < 1` there is a root `r_0 ∈ (0, 1)`
of `z = β(z)`, it is the only root of `z = β(z)` in the open unit disk, the geometric vector
`q_n = (1 - r_0) r_0^n` solves `qP = q`, `qe = 1`, and it is the only probability vector that does. -/
theorem arrival_point_geometric (A : Measure ℝ) (lam mu : ℝ) (hlam : 0 < lam) (hmu : 0 < mu)
    (hA : IsInterarrivalLaw A lam) (hrho : lam / mu < 1) :
    ∃ r0 : ℝ, r0 ∈ Set.Ioo (0 : ℝ) 1 ∧ beta A mu (r0 : ℂ) = (r0 : ℂ) ∧
      (∀ z : ℂ, ‖z‖ < 1 → beta A mu z = z → z = (r0 : ℂ)) ∧
      IsArrivalPointStationary A mu (fun n => (1 - r0) * r0 ^ n) ∧
      ∀ q : ℕ → ℝ, IsArrivalPointStationary A mu q → q = fun n => (1 - r0) * r0 ^ n := by sorry

end QueueingFundamentals.GM1
