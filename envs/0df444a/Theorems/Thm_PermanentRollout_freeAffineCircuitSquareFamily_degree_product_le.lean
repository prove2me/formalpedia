-- Prove2me | Theorems.Thm_PermanentRollout_freeAffineCircuitSquareFamily_degree_product_le
-- name    : PermanentRollout.freeAffineCircuitSquareFamily_degree_product_le
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:56:39.904517+00:00
-- url     : https://prove2.me/theorems/6b606603-dbec-4867-93c2-386b576b8fc2
-- title:
--   PermanentRollout.freeAffineCircuitSquareFamily_degree_product_le
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | Permanent | external Lean 4.33.1 validation; bundle SHA256 8a836240c656ca1eb46e7ecec147014a94283bee53230c4428d90fa24026d93c

import Mathlib
import Definitions.Def_Permanent
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentRollout
open scoped BigOperators
noncomputable section

theorem PermanentRollout.freeAffineCircuitSquareFamily_degree_product_le
    {k : ℕ} (circuit : FreeAffineCircuit (Fin k))
    (output : Fin k → FreeAffineForm (Fin k)) (target : Fin k → ℂ) :
    (∏ i,
      (freeAffineCircuitSquareFamily circuit output target i).totalDegree) ≤
      2 ^ circuit.multiplicationCount := by sorry
