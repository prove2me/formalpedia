-- Prove2me | Theorems.Thm_PermanentRollout_ReverseAdjoint_CircuitAdjoint_foldl_realizes
-- name    : PermanentRollout.ReverseAdjoint.CircuitAdjoint.foldl_realizes
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:56:37.782607+00:00
-- url     : https://prove2.me/theorems/e427b604-31d7-4e31-a3bb-171f050c485b
-- title:
--   PermanentRollout.ReverseAdjoint.CircuitAdjoint.foldl_realizes
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

theorem PermanentRollout.ReverseAdjoint.CircuitAdjoint.foldl_realizes {ι : Type*}
    (instructions : List (FreeAffineInstruction ι × ℕ))
    (state : CircuitAdjoint ι) (adjoints : ReverseAdjoint ι)
    (sourceValues : Array (MvPolynomial ι ℂ))
    (hposition : ∀ instruction ∈ instructions,
      instruction.2 < state.sourceLength)
    (hvalid : ∀ instruction ∈ instructions,
      instruction.1.referencesBounded instruction.2)
    (hforward : ∀ gate, gate < state.sourceLength →
      state.circuit.values.getD gate 0 = sourceValues.getD gate 0)
    (hinput : ∀ input,
      (state.inputAdjoints input).eval state.circuit.values =
        adjoints.inputAdjoints input)
    (hgate : ∀ gate,
      (state.gateAdjoints gate).eval state.circuit.values =
        adjoints.gateAdjoints gate) :
    (∀ gate, gate < state.sourceLength →
      (instructions.foldl step state).circuit.values.getD gate 0 =
        sourceValues.getD gate 0) ∧
    (∀ input,
      ((instructions.foldl step state).inputAdjoints input).eval
        (instructions.foldl step state).circuit.values =
          (instructions.foldl
            (ReverseAdjoint.step sourceValues) adjoints).inputAdjoints
              input) ∧
    (∀ gate,
      ((instructions.foldl step state).gateAdjoints gate).eval
        (instructions.foldl step state).circuit.values =
          (instructions.foldl
            (ReverseAdjoint.step sourceValues) adjoints).gateAdjoints
              gate) := by sorry
