-- Prove2me | Theorems.Thm_PermanentRollout_ReverseAdjoint_CircuitAdjoint_foldl_multiplicationCount
-- name    : PermanentRollout.ReverseAdjoint.CircuitAdjoint.foldl_multiplicationCount
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:56:37.782607+00:00
-- url     : https://prove2.me/theorems/5e6b4803-aeb3-4612-b6c7-b8d8263dc1fa
-- title:
--   PermanentRollout.ReverseAdjoint.CircuitAdjoint.foldl_multiplicationCount
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

theorem PermanentRollout.ReverseAdjoint.CircuitAdjoint.foldl_multiplicationCount {ι : Type*}
    (instructions : List (FreeAffineInstruction ι × ℕ))
    (state : CircuitAdjoint ι)
    (hposition : ∀ instruction ∈ instructions,
      instruction.2 < state.sourceLength)
    (hvalid : ∀ instruction ∈ instructions,
      instruction.1.referencesBounded instruction.2) :
    (instructions.foldl step state).circuit.multiplicationCount =
      state.circuit.multiplicationCount +
        (instructions.map (fun instruction =>
          ReverseAdjoint.instructionCost instruction.1)).sum := by sorry
