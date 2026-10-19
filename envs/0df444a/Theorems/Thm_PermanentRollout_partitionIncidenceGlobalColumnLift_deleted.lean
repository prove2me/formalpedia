-- Prove2me | Theorems.Thm_PermanentRollout_partitionIncidenceGlobalColumnLift_deleted
-- name    : PermanentRollout.partitionIncidenceGlobalColumnLift_deleted
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:56:39.904517+00:00
-- url     : https://prove2.me/theorems/d34443fb-0420-4bb9-aa24-a97c916689b6
-- title:
--   PermanentRollout.partitionIncidenceGlobalColumnLift_deleted
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | Permanent | external Lean 4.33.1 validation; bundle SHA256 8a836240c656ca1eb46e7ecec147014a94283bee53230c4428d90fa24026d93c

import Mathlib
import Definitions.Def_Permanent
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentRollout
open scoped BigOperators

theorem PermanentRollout.partitionIncidenceGlobalColumnLift_deleted
    (t s d : ℕ) (a : Fin s) (i : Fin t) (q : ℕ) :
    partitionIncidenceGlobalColumnLift t s d
      (MvPolynomial.rename
        (fun row : Fin t => (Sum.inr (a, row) : IncidenceCoordinate t s))
        (deletedCoordinateEsymmPolynomial t q i)) =
      MvPolynomial.map
        (algebraMap ℂ ((MvPolynomial (IncidenceRowBlock t ⊕ (Fin s × Fin (d - 2))) ℂ)))
        (MvPolynomial.rename
          (fun row : Fin t => (a, row))
          (deletedCoordinateEsymmPolynomial t q i)) := by sorry
