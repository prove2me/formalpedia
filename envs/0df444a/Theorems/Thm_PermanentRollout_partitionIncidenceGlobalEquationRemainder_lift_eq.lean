-- Prove2me | Theorems.Thm_PermanentRollout_partitionIncidenceGlobalEquationRemainder_lift_eq
-- name    : PermanentRollout.partitionIncidenceGlobalEquationRemainder_lift_eq
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:56:39.904517+00:00
-- url     : https://prove2.me/theorems/37141623-bde9-44dd-8623-adcf14c7275b
-- title:
--   PermanentRollout.partitionIncidenceGlobalEquationRemainder_lift_eq
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | Permanent | external Lean 4.33.1 validation; bundle SHA256 8a836240c656ca1eb46e7ecec147014a94283bee53230c4428d90fa24026d93c

import Mathlib
import Definitions.Def_Permanent
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentRollout
open scoped BigOperators

theorem PermanentRollout.partitionIncidenceGlobalEquationRemainder_lift_eq
    (t s d : ℕ) (a : Fin s) (i : Fin t) :
    partitionIncidenceGlobalColumnLift t s d
      (partitionIncidenceGlobalEquationRemainder t s d a i) =
      incidenceUniversalPartitionDerivative d i
        (partitionIncidenceGlobalUniversalParameter t s d)
        (fun row : Fin t => (a, row)) -
      MvPolynomial.C
        (algebraMap ℂ ((MvPolynomial (IncidenceRowBlock t ⊕ (Fin s × Fin (d - 2))) ℂ))
          (((-1 : ℂ) ^ (d - 1)) * ((d - 1).factorial : ℂ))) *
      MvPolynomial.map
        (algebraMap ℂ ((MvPolynomial (IncidenceRowBlock t ⊕ (Fin s × Fin (d - 2))) ℂ)))
        (MvPolynomial.rename
          (fun row : Fin t => (a, row))
          (deletedCoordinateEsymmPolynomial t (d - 1) i)) := by sorry
