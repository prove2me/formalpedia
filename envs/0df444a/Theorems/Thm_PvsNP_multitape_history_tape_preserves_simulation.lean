-- Prove2me | Theorems.Thm_PvsNP_multitape_history_tape_preserves_simulation
-- name    : PvsNP.multitape_history_tape_preserves_simulation
-- status  : Proved
-- author  : @Jie Luo
-- created : 2026-11-26T10:43:56.848144+00:00
-- url     : https://prove2.me/theorems/a2ceeefa-bd73-5b15-92b0-7122db60d4b0
-- title:
--   Recording input history on a new work tape preserves multitape simulation
-- statement:
--   Extend a deterministic multitape machine by prepending a work tape whose current cell remains blank. Whenever a transition moves the input head right from a nonblank symbol, it writes that symbol on the added tape and advances the new work head to the next blank cell. Otherwise it leaves that tape untouched. The extension preserves the output and halt flag for every input and every step count.
-- source:
--   Input-history variant of the fresh-square history tape technique in C. H. Bennett, Logical Reversibility of Computation, IBM J. Res. Dev. 17 (1973), pp. 525–532, proof following Table 1, https://www.dna.caltech.edu/courses/cs191/paperscs191/bennett1973.pdf. The exact transition operation here is defined in the Prove2Me multitape model.

import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Universal_Basic
import Mathlib
open Turing.MultiTapeTM.Universal

theorem PvsNP.multitape_history_tape_preserves_simulation (d : Desc) (x : List ℕ) (t : ℕ) :
    simulate ⟨d.tapes+1,d.q₀,d.table.map (fun row =>
      ({row.1 with work := none :: row.1.work},
        {row.2 with workTapes :=
          (match (match row.2.inputTape with | .pos => row.1.input | _ => none) with
           | none => (none,.zero)
           | some b => (some (some b),.pos)) :: row.2.workTapes}))⟩ x t = simulate d x t := by sorry
