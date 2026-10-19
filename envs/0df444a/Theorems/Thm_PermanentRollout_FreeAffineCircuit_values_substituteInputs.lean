-- Prove2me | Theorems.Thm_PermanentRollout_FreeAffineCircuit_values_substituteInputs
-- name    : PermanentRollout.FreeAffineCircuit.values_substituteInputs
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:56:37.133993+00:00
-- url     : https://prove2.me/theorems/15bcc9d3-c4ad-45ad-87ca-5ca0da5baf9d
-- title:
--   PermanentRollout.FreeAffineCircuit.values_substituteInputs
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
open PermanentRollout.FreeAffineCircuit

theorem PermanentRollout.FreeAffineCircuit.values_substituteInputs {ι κ : Type*}
    (circuit : FreeAffineCircuit ι)
    (substitution : ι → FreeAffineInput κ) :
    (circuit.substituteInputs substitution).values =
      circuit.values.map
        (MvPolynomial.aeval
          (fun index => (substitution index).polynomial)) := by sorry
