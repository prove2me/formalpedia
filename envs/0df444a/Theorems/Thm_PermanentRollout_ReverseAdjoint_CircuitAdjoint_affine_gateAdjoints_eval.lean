-- Prove2me | Theorems.Thm_PermanentRollout_ReverseAdjoint_CircuitAdjoint_affine_gateAdjoints_eval
-- name    : PermanentRollout.ReverseAdjoint.CircuitAdjoint.affine_gateAdjoints_eval
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:56:37.133993+00:00
-- url     : https://prove2.me/theorems/18b0b658-2fe2-4355-918d-03ccb63c76e8
-- title:
--   PermanentRollout.ReverseAdjoint.CircuitAdjoint.affine_gateAdjoints_eval
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

theorem PermanentRollout.ReverseAdjoint.CircuitAdjoint.affine_gateAdjoints_eval {ι : Type*}
    (state : CircuitAdjoint ι) (position : ℕ)
    (form : FreeAffineForm ι) (gate : ℕ) :
    ((state.affine position form).gateAdjoints gate).eval
        (state.affine position form).circuit.values =
      if gate = position then 0 else
        (state.gateAdjoints gate).eval state.circuit.values +
          MvPolynomial.C (form.gateCoefficients gate) *
            (state.gateAdjoints position).eval state.circuit.values := by sorry
