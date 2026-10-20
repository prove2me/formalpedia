-- Prove2me | Theorems.Thm_PermanentRollout_freeAffineCircuitInstructionEquation_totalDegree_le
-- name    : PermanentRollout.freeAffineCircuitInstructionEquation_totalDegree_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:38.420988+00:00
-- url     : https://prove2.me/theorems/7e97b69b-64f2-4972-8677-e0744edbc7b5
-- title:
--   PermanentRollout.freeAffineCircuitInstructionEquation_totalDegree_le
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

theorem PermanentRollout.freeAffineCircuitInstructionEquation_totalDegree_le
    {k : ℕ} (circuit : FreeAffineCircuit (Fin k))
    (j : Fin circuit.program.length) :
    (freeAffineCircuitInstructionEquation circuit j).totalDegree ≤
      if (circuit.program.get j).isMultiplication then 2 else 1 := by sorry
