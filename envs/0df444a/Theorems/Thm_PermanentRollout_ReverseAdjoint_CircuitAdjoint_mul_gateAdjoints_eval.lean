-- Prove2me | Theorems.Thm_PermanentRollout_ReverseAdjoint_CircuitAdjoint_mul_gateAdjoints_eval
-- name    : PermanentRollout.ReverseAdjoint.CircuitAdjoint.mul_gateAdjoints_eval
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:37.782607+00:00
-- url     : https://prove2.me/theorems/bce5aa2d-f83c-49d9-96aa-f21a3f59c08f
-- title:
--   PermanentRollout.ReverseAdjoint.CircuitAdjoint.mul_gateAdjoints_eval
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

theorem PermanentRollout.ReverseAdjoint.CircuitAdjoint.mul_gateAdjoints_eval {ι : Type*}
    (state : CircuitAdjoint ι) (position left right : ℕ)
    (hleft : left < state.sourceLength)
    (hright : right < state.sourceLength) (gate : ℕ) :
    ((state.mul position left right hleft hright).gateAdjoints gate).eval
        (state.mul position left right hleft hright).circuit.values =
      (if gate = position then 0 else
        (state.gateAdjoints gate).eval state.circuit.values) +
      (if gate = left then
        (state.gateAdjoints position).eval state.circuit.values *
          state.circuit.values.getD right 0 else 0) +
      (if gate = right then
        (state.gateAdjoints position).eval state.circuit.values *
          state.circuit.values.getD left 0 else 0) := by sorry
