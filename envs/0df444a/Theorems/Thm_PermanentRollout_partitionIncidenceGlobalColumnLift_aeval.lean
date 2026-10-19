-- Prove2me | Theorems.Thm_PermanentRollout_partitionIncidenceGlobalColumnLift_aeval
-- name    : PermanentRollout.partitionIncidenceGlobalColumnLift_aeval
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:56:39.173076+00:00
-- url     : https://prove2.me/theorems/8d7bdac9-758c-4f13-bc89-497211c5c8b0
-- title:
--   PermanentRollout.partitionIncidenceGlobalColumnLift_aeval
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | Permanent | external Lean 4.33.1 validation; bundle SHA256 8a836240c656ca1eb46e7ecec147014a94283bee53230c4428d90fa24026d93c

import Mathlib
import Definitions.Def_Permanent
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentRollout
open scoped BigOperators

theorem PermanentRollout.partitionIncidenceGlobalColumnLift_aeval
    (t s d : ℕ) (f : MvPolynomial (IncidenceCoordinate t s) ℂ) :
    letI := partitionIncidenceGlobalBaseAlgebra t s d
    MvPolynomial.aeval
      (fun coordinate : Fin s × Fin t =>
        Ideal.Quotient.mk (partitionIncidenceIdeal t s d)
          (MvPolynomial.X (Sum.inr coordinate)))
      (partitionIncidenceGlobalColumnLift t s d f) =
      Ideal.Quotient.mk (partitionIncidenceIdeal t s d) f := by sorry
