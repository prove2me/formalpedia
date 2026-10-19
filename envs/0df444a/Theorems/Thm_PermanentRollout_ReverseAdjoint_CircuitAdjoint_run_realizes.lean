-- Prove2me | Theorems.Thm_PermanentRollout_ReverseAdjoint_CircuitAdjoint_run_realizes
-- name    : PermanentRollout.ReverseAdjoint.CircuitAdjoint.run_realizes
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:56:37.782607+00:00
-- url     : https://prove2.me/theorems/6ece3b17-14db-4480-bb35-b02859518fa5
-- title:
--   PermanentRollout.ReverseAdjoint.CircuitAdjoint.run_realizes
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

theorem PermanentRollout.ReverseAdjoint.CircuitAdjoint.run_realizes {ι : Type*}
    (circuit : FreeAffineCircuit ι) (output : FreeAffineForm ι) :
    (∀ gate, gate < circuit.program.length →
      (run circuit output).circuit.values.getD gate 0 =
        circuit.values.getD gate 0) ∧
    (∀ input,
      ((run circuit output).inputAdjoints input).eval
        (run circuit output).circuit.values =
          (ReverseAdjoint.run circuit output).inputAdjoints input) ∧
    (∀ gate,
      ((run circuit output).gateAdjoints gate).eval
        (run circuit output).circuit.values =
          (ReverseAdjoint.run circuit output).gateAdjoints gate) := by sorry
