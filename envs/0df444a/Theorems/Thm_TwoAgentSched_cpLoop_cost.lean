-- Prove2me | Theorems.Thm_TwoAgentSched_cpLoop_cost
-- name    : TwoAgentSched.cpLoop_cost
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-30T03:53:04.564764+00:00
-- url     : https://prove2.me/theorems/c2df4d98-73c8-4797-9ae5-272c4ac18286
-- title:
--   p. 233: the A-scan happens at most $n_A$ times
-- statement:
--   There is an absolute constant $C$ such that:
--
--   1. one A-scan (evaluate $f^A_h(\bar\tau)$ for every unscheduled A-job, keep the first minimizer, remove it) over a list $As$ costs at most $C\,|As|$ unit steps;
--   2. the main loop of the §4 algorithm, started from any state with $|As|$ unscheduled A-jobs and $|Bs|$ unscheduled B-jobs (any $\bar\tau$, deadlines and partial output), costs at most
--   $$
--   C\cdot\bigl(|As|^2 + |As| + |Bs| + 1\bigr)
--   $$
--   unit steps.
--
--   Every B-step costs $O(1)$ and removes a B-job, and each of the at most $|As|$ A-scans tries all unscheduled A-jobs; this is the paper's count "Because this happens $n_A$ times".
--
--   Differences from the source:
--   - reading: all unscheduled A-jobs may have to be tried out, and this happens n_A times → the cost of one A-scan is O(|As|), and the main loop costs O(|As|^2 + |As| + |Bs| + 1) from any state; reason: the count of scans turned into the cost of the loop, which is what the running-time bound uses
--   - reading: time, assuming each f^A_h(·) value can be computed in constant time and the deadlines are available (p. 233) → the cost of the Timed run: one step per real addition or subtraction, per comparison (reals, cuts), per evaluation f^A_h(t), per deadline lookup, per list cell traversed, consed or moved, per relation query or array access; reason: the unit-cost RAM model with the paper's constant-time assumptions; the deadlines are an input, as in the paper's case where f^B_k^{-1} is available
--   - reading: O(·) → one absolute constant C, chosen before all other quantities; reason: the O-notation of an algorithm analysis is a constant independent of the input
-- source:
--   Agnetis, Mirchandani, Pacciarelli, Pacifici, Scheduling Problems with Two Competing Agents, Operations Research 52(2) (2004), p. 233 ("whenever no B-job can be scheduled, all unscheduled A-jobs may have to be tried out. Because this happens n_A times")

import Mathlib
import Definitions.Def_TwoAgentSched_Timed
import Definitions.Def_TwoAgentSched_Feasible
import Definitions.Def_TwoAgentSched_cpAlgo

namespace TwoAgentSched

/-- **The A-scan happens at most `n_A` times** (Agnetis–Mirchandani–Pacciarelli–Pacifici, Oper.
Res. 52(2) (2004), p. 233: "whenever no B-job can be scheduled, all unscheduled A-jobs may have to
be tried out. Because this happens `n_A` times"). There is one absolute constant `C` such that
1. one A-scan over a list `As` of unscheduled A-jobs costs at most `C · |As|`;
2. the main loop `cpLoop`, from any state with `|As|` unscheduled A-jobs and `|Bs|` unscheduled
   B-jobs (any fuel, `τ̄`, deadlines and partial output), costs at most
   `C · (|As|² + |As| + |Bs| + 1)`. -/
theorem cpLoop_cost :
    ∃ C : ℝ,
      (∀ (nA : ℕ) (fA : Fin nA → ℝ → ℝ) (τ : ℝ) (As : List (Fin nA)),
        ((scanA fA τ As).cost : ℝ) ≤ C * (As.length : ℝ)) ∧
      ∀ (nA nB : ℕ) (p : Job nA nB → ℝ) (fA : Fin nA → ℝ → ℝ)
        (D : Fin nB → WithTop (ℝ ×ₗ Bool)) (fuel : ℕ) (τ : ℝ) (As : List (Fin nA))
        (Bs : List (Fin nB)) (acc : List (Job nA nB)),
        ((cpLoop p fA D fuel τ As Bs acc).cost : ℝ) ≤
          C * ((As.length : ℝ) ^ 2 + (As.length : ℝ) + (Bs.length : ℝ) + 1) := by sorry

end TwoAgentSched
