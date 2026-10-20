-- Prove2me | Theorems.Thm_PermanentRollout_ReverseAdjoint_CircuitAdjoint_mul_new_left
-- name    : PermanentRollout.ReverseAdjoint.CircuitAdjoint.mul_new_left
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:37.782607+00:00
-- url     : https://prove2.me/theorems/322b5c0f-fb70-46c9-8ef8-fdf250d6979c
-- title:
--   PermanentRollout.ReverseAdjoint.CircuitAdjoint.mul_new_left
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

theorem PermanentRollout.ReverseAdjoint.CircuitAdjoint.mul_new_left {ι : Type*}
    (state : CircuitAdjoint ι) (position left right : ℕ)
    (hleft : left < state.sourceLength)
    (hright : right < state.sourceLength) :
    (state.mul position left right hleft hright).circuit.values.getD
        (state.circuit.program.length + 2) 0 =
      (state.gateAdjoints position).eval state.circuit.values *
        state.circuit.values.getD left 0 := by sorry
