-- Prove2me | Theorems.Thm_PermanentRollout_partitionIncidenceGlobalPowerRemainder_aeval
-- name    : PermanentRollout.partitionIncidenceGlobalPowerRemainder_aeval
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:39.173076+00:00
-- url     : https://prove2.me/theorems/b8e7e167-728a-4507-b018-9fcde729d363
-- title:
--   PermanentRollout.partitionIncidenceGlobalPowerRemainder_aeval
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | Permanent | external Lean 4.33.1 validation; bundle SHA256 8a836240c656ca1eb46e7ecec147014a94283bee53230c4428d90fa24026d93c

import Mathlib
import Definitions.Def_Permanent
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentRollout
open scoped BigOperators

theorem PermanentRollout.partitionIncidenceGlobalPowerRemainder_aeval
    {t s d : ℕ} (hd : 3 ≤ d) (ht : d ≤ t)
    (coordinate : Fin s × Fin t) :
    letI := partitionIncidenceGlobalBaseAlgebra t s d
    (Ideal.Quotient.mk (partitionIncidenceIdeal t s d)
      (MvPolynomial.X (Sum.inr coordinate))) ^ (d - 1) =
      MvPolynomial.aeval
        (fun row : Fin s × Fin t =>
          Ideal.Quotient.mk (partitionIncidenceIdeal t s d)
            (MvPolynomial.X (Sum.inr row)))
        (partitionIncidenceGlobalPowerRemainder t s d coordinate) := by sorry
