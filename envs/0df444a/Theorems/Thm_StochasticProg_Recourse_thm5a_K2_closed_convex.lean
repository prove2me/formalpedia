-- Prove2me | Theorems.Thm_StochasticProg_Recourse_thm5a_K2_closed_convex
-- name    : StochasticProg.Recourse.thm5a_K2_closed_convex
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-18T04:47:03.7228+00:00
-- url     : https://prove2.me/theorems/c7242119-ee33-43c6-836f-d8cfcc31a67e
-- title:
--   Chapter 3, Theorem 5(a) -- K2 is closed and convex
-- statement:
--   **Chapter 3, Theorem 5(a).** For a two-stage recourse instance with fixed recourse matrix $W$
--   and a finite scenario set, the second-stage feasibility set
--   $$K_2 = \{x \mid Q(x) < \infty\}$$
--   is closed and convex.
--
--   This is the book's structural fact underlying every later optimality result of the chapter: the
--   constraint set of the deterministic-equivalent program (1.2) is well-behaved (closed, convex)
--   before anything is said about the recourse value $Q$ itself.
--
--   **Formalization Note.** The book states Theorem 5 for a general random vector $\xi$ with finite
--   second moments; under the finite-scenario model `Fin K` used throughout this mission, "finite
--   second moments" holds automatically, so the hypothesis does not appear as a separate argument.
-- source:
--   Birge & Louveaux, Introduction to Stochastic Programming, 2nd ed., Springer 2011, p. 111, Chapter 3, Theorem 5(a)

import Mathlib
import Definitions.Def_StochasticProg_Recourse_Instance

namespace StochasticProg.Recourse

variable {n1 n2 m1 m2 K : ℕ}

/-- Chapter 3, Theorem 5(a) (p. 111): for a fixed recourse matrix `W` and a finite
scenario set (finite second moments are automatic), the second-stage feasibility
set `K2` is closed and convex. -/
theorem thm5a_K2_closed_convex (inst : Instance n1 n2 m1 m2 K) :
    IsClosed (K2 inst) ∧ Convex ℝ (K2 inst) := by sorry

end StochasticProg.Recourse
