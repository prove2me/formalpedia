-- Prove2me | Theorems.Thm_PermanentRollout_ReverseAdjoint_CircuitAdjoint_step_multiplicationCount
-- name    : PermanentRollout.ReverseAdjoint.CircuitAdjoint.step_multiplicationCount
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:37.782607+00:00
-- url     : https://prove2.me/theorems/00aa6a30-93d6-4a05-b195-cc75adf6a07a
-- title:
--   PermanentRollout.ReverseAdjoint.CircuitAdjoint.step_multiplicationCount
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | Permanent | external Lean 4.33.1 validation; bundle SHA256 8a836240c656ca1eb46e7ecec147014a94283bee53230c4428d90fa24026d93c

import Mathlib
import Definitions.Def_Permanent
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentRollout
noncomputable section
open scoped BigOperators
open PermanentRollout.ReverseAdjoint
open PermanentRollout.ReverseAdjoint.CircuitAdjoint

theorem PermanentRollout.ReverseAdjoint.CircuitAdjoint.step_multiplicationCount {ι : Type*}
    (state : CircuitAdjoint ι)
    (instruction : FreeAffineInstruction ι × ℕ)
    (hposition : instruction.2 < state.sourceLength)
    (hvalid : instruction.1.referencesBounded instruction.2) :
    (step state instruction).circuit.multiplicationCount =
      state.circuit.multiplicationCount +
        ReverseAdjoint.instructionCost instruction.1 := by sorry
