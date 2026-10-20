-- Prove2me | Theorems.Thm_PermanentRollout_blockIncidencePowerRemainder_aeval
-- name    : PermanentRollout.blockIncidencePowerRemainder_aeval
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:39.904517+00:00
-- url     : https://prove2.me/theorems/ad591311-7c13-4fe9-b6e1-2acafa91d6cb
-- title:
--   PermanentRollout.blockIncidencePowerRemainder_aeval
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | Permanent | external Lean 4.33.1 validation; bundle SHA256 8a836240c656ca1eb46e7ecec147014a94283bee53230c4428d90fa24026d93c

import Mathlib
import Definitions.Def_Permanent
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentRollout
open scoped BigOperators

theorem PermanentRollout.blockIncidencePowerRemainder_aeval
    {b t s d : ℕ} (hd : 3 ≤ d) (ht : d ≤ t)
    (coordinate : Fin b × (Fin s × Fin t)) :
    letI := blockIncidenceBaseAlgebra b t s d
    (Ideal.Quotient.mk (blockIncidenceIdeal b t s d)
      (MvPolynomial.X (coordinate.1, Sum.inr coordinate.2))) ^ (d - 1) =
      MvPolynomial.aeval
        (fun row : Fin b × (Fin s × Fin t) =>
          Ideal.Quotient.mk (blockIncidenceIdeal b t s d)
            (MvPolynomial.X (row.1, Sum.inr row.2)))
        (blockIncidencePowerRemainder b t s d coordinate) := by sorry
