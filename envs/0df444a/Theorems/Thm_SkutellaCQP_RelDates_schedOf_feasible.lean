-- Prove2me | Theorems.Thm_SkutellaCQP_RelDates_schedOf_feasible
-- name    : SkutellaCQP.RelDates.schedOf_feasible
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T01:12:07.883988+00:00
-- url     : https://prove2.me/theorems/9f1d3026-376a-4bec-b771-e6541e0a4185
-- title:
--   §3.1, p. 16 — a feasible assignment to time slots defines a feasible schedule with completion times (17)
-- statement:
--   Let $\tau$ be a feasible assignment of jobs to time slots: every job $j$ is assigned to a slot $i_k$ with $\rho_{i_k} \ge r_{ij}$. Construct a schedule by sequencing the jobs of each slot $i_k$ according to $\prec_i$ and starting the slot at
--   $$s_{i_1} := \rho_{i_1},\qquad s_{i_{k+1}} := \max\Big\{\rho_{i_{k+1}},\ s_{i_k} + \sum_{j \in i_k} p_{ij}\Big\},$$
--   so that job $j \in i_k$ completes at $C_j = s_{i_k} + p_{ij} + \sum_{j' \prec_i j,\ j' \in i_k} p_{ij'}$, which is (17). Then this schedule is a feasible nonpreemptive schedule (no job starts before its release date, no two jobs overlap on a machine), and its completion times are exactly the values (17).
--
--   This is the step that makes the output of randomized rounding a schedule: rounding produces a feasible slot assignment, not a schedule, and this statement converts one into the other.
--
--   **Formalization Note.** Standing assumptions $p_{ij} > 0$, $w_j \ge 0$, $r_{ij} \ge 0$ are hypotheses.
-- source:
--   Skutella, Convex quadratic and semidefinite programming relaxations in scheduling, J. ACM 48 (2001), p. 16, §3.1, first paragraph

import Mathlib
import Definitions.Def_SkutellaCQP_RelDates_Setting

namespace SkutellaCQP.RelDates

open Finset

/-- p. 16: the schedule built from a feasible slot assignment is a feasible schedule, and its
completion times are given by (17). -/
theorem schedOf_feasible {m n : ℕ} (p : Fin m → Fin n → ℝ) (w : Fin n → ℝ) (r : Fin m → Fin n → ℝ)
    (hp : ∀ i j, 0 < p i j) (hw : ∀ j, 0 ≤ w j) (hr : ∀ i j, 0 ≤ r i j)
    (τ : Fin n → Fin m × Fin n) (hτ : SlotFeasible r τ) :
    SFeasible p r (schedOf p w r τ) ∧ ∀ j, compl p (schedOf p w r τ) j = Cslot p w r τ j := by sorry

end SkutellaCQP.RelDates
