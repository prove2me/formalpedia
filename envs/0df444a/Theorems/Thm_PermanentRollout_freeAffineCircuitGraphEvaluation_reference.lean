-- Prove2me | Theorems.Thm_PermanentRollout_freeAffineCircuitGraphEvaluation_reference
-- name    : PermanentRollout.freeAffineCircuitGraphEvaluation_reference
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:38.420988+00:00
-- url     : https://prove2.me/theorems/8e0b4488-4f3b-4a22-9149-cfbe9feaf321
-- title:
--   PermanentRollout.freeAffineCircuitGraphEvaluation_reference
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

theorem PermanentRollout.freeAffineCircuitGraphEvaluation_reference
    {k : ℕ} (circuit : FreeAffineCircuit (Fin k)) (r : ℕ) :
    freeAffineCircuitGraphEvaluation circuit
      (freeAffineGateReference
        (k := k) (n := circuit.program.length) r) =
      circuit.values.getD r 0 := by sorry
