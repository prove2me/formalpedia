-- Prove2me | Theorems.Thm_PNormReg_run_work_le
-- name    : PNormReg.run_work_le
-- status  : Proved
-- author  : @Mr Robbins
-- created : 2026-11-23T02:51:53.876187+00:00
-- url     : https://prove2.me/theorems/451051ef-ed4c-4169-a96e-29d05c536aa5
-- title:
--   The work counter grows by at most the number of steps
-- statement:
--   For every PNormReg program $P$, machine state $s$, coin tape $\omega$, and number of steps $t$, the work counter after the run satisfies
--
--   $$
--   \operatorname{work}(\operatorname{run}(P,s,\omega,t))\le \operatorname{work}(s)+t.
--   $$
--
--   Thus a run of virtual length $t$ can increase the exact work counter by at most $t$, regardless of whether and when the machine halts. This elementary accounting bound is used when transferring virtual running-time estimates to relocated program calls in the composed nearest-neighbor data structure.
--
--   **Formalization Note** `work` is the natural-number counter in `PNormReg.State`; a halted state stutters without further work.
-- source:
--   Original PNormReg machine-library lemma written for the mission 'Deterministic Approximate Nearest Neighbors in High Dimensions'; supports the program composition in Feng--Indyk, STOC 2027 submission, §7.4, p.19. Follows directly from PNormReg.step in definition PNormReg_Machine (one unit of work per executed instruction, none after halt).

import Mathlib
import Definitions.Def_PNormReg_Machine

namespace PNormReg

/-- For any program, initial state, coin tape and step count, the final work counter exceeds the
initial work counter by at most the number of steps. -/
theorem run_work_le (P : Program) (s : State) (ω : ℕ → Bool) (t : ℕ) :
    (run P s ω t).work ≤ s.work + t := by sorry
