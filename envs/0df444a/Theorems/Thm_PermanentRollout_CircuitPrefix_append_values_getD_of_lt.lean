-- Prove2me | Theorems.Thm_PermanentRollout_CircuitPrefix_append_values_getD_of_lt
-- name    : PermanentRollout.CircuitPrefix.append_values_getD_of_lt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:40.650338+00:00
-- url     : https://prove2.me/theorems/0a19f4c3-6107-4c38-baf6-446d983f66f8
-- title:
--   PermanentRollout.CircuitPrefix.append_values_getD_of_lt
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | Permanent | external Lean 4.33.1 validation; bundle SHA256 8a836240c656ca1eb46e7ecec147014a94283bee53230c4428d90fa24026d93c

import Mathlib
import Definitions.Def_Permanent
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentRollout
open scoped BigOperators
noncomputable section
open PermanentRollout.CircuitPrefix

theorem PermanentRollout.CircuitPrefix.append_values_getD_of_lt {ι : Type} (state : CircuitPrefix ι)
    (instruction : Instruction ι)
    (hvalid : instruction.referencesBounded state.program.length)
    (index : ℕ) (hindex : index < state.program.length) :
    (state.append instruction hvalid).values.getD index 0 =
      state.values.getD index 0 := by sorry
