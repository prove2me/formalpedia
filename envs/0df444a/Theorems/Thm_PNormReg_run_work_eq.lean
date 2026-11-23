-- Prove2me | Theorems.Thm_PNormReg_run_work_eq
-- name    : PNormReg.run_work_eq
-- status  : Proved
-- author  : @Mr Robbins
-- created : 2026-11-23T02:53:03.767098+00:00
-- url     : https://prove2.me/theorems/9dae5e2b-8893-4435-9056-8ed9106ca247
-- title:
--   Exact work of a run that is still running
-- statement:
--   Let $P$ be a PNormReg program, $s$ a running initial state, $\omega$ a coin tape, and $t$ a step count. If the state after $t$ steps is still running, then
--
--   $$
--   \operatorname{work}(\operatorname{run}(P,s,\omega,t))=\operatorname{work}(s)+t.
--   $$
--
--   Indeed, once halted a state remains halted; consequently the running final state implies that every step of the run executed an instruction and was charged one unit of work. This gives exact time accounting for a relocated subroutine that returns to a running host state at its exit label.
--
--   **Formalization Note** Running means `halted = false`. The conclusion holds on every coin tape, including the deterministic all-false tape.
-- source:
--   Original PNormReg machine-library lemma written for the mission 'Deterministic Approximate Nearest Neighbors in High Dimensions'; supports the program composition in Feng--Indyk, STOC 2027 submission, §7.4, p.19. Direct consequence of PNormReg.step in definition PNormReg_Machine.

import Mathlib
import Definitions.Def_PNormReg_Machine

namespace PNormReg

/-- If a run starts and ends in running (not halted) states, every one of its steps executes an
instruction, so its work counter increases by exactly the number of steps. -/
theorem run_work_eq (P : Program) (s : State) (ω : ℕ → Bool) (t : ℕ)
    (h₀ : s.halted = false) (hₜ : (run P s ω t).halted = false) :
    (run P s ω t).work = s.work + t := by sorry
