-- Prove2me | Theorems.Thm_PermanentRollout_freeAffineCircuitGraphEvaluation_extendedForm
-- name    : PermanentRollout.freeAffineCircuitGraphEvaluation_extendedForm
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:38.420988+00:00
-- url     : https://prove2.me/theorems/bd2ec76b-4060-4062-a51a-9060204810b7
-- title:
--   PermanentRollout.freeAffineCircuitGraphEvaluation_extendedForm
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | Permanent | external Lean 4.33.1 validation; bundle SHA256 8a836240c656ca1eb46e7ecec147014a94283bee53230c4428d90fa24026d93c

import Mathlib
import Definitions.Def_Permanent
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentRollout
open scoped BigOperators Topology Pointwise
open Filter Asymptotics
attribute [local instance] MvPolynomial.gradedAlgebra

theorem PermanentRollout.freeAffineCircuitGraphEvaluation_extendedForm
    {k : ℕ} (circuit : FreeAffineCircuit (Fin k))
    (form : FreeAffineForm (Fin k)) :
    freeAffineCircuitGraphEvaluation circuit
      (freeAffineExtendedForm
        (n := circuit.program.length) form) =
      form.eval circuit.values := by sorry
