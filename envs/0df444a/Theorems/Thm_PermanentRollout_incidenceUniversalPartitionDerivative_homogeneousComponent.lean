-- Prove2me | Theorems.Thm_PermanentRollout_incidenceUniversalPartitionDerivative_homogeneousComponent
-- name    : PermanentRollout.incidenceUniversalPartitionDerivative_homogeneousComponent
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:56:39.173076+00:00
-- url     : https://prove2.me/theorems/d7aafe40-a5d9-4aa0-a450-8a7a3dcd8ac1
-- title:
--   PermanentRollout.incidenceUniversalPartitionDerivative_homogeneousComponent
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | Permanent | external Lean 4.33.1 validation; bundle SHA256 8a836240c656ca1eb46e7ecec147014a94283bee53230c4428d90fa24026d93c

import Mathlib
import Definitions.Def_Permanent
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentRollout
open scoped BigOperators

theorem PermanentRollout.incidenceUniversalPartitionDerivative_homogeneousComponent
    {t : ℕ} {ι B : Type*} [CommRing B] [Algebra ℂ B]
    (d : ℕ) (i : Fin t)
    (parameter : Finset (Fin t) → B) (index : Fin t → ι) :
    MvPolynomial.homogeneousComponent (d - 1)
      (incidenceUniversalPartitionDerivative d i parameter index) =
      MvPolynomial.C
          (algebraMap ℂ B
            (((-1 : ℂ) ^ (d - 1)) * ((d - 1).factorial : ℂ))) *
        MvPolynomial.map (algebraMap ℂ B)
          (MvPolynomial.rename index
            (deletedCoordinateEsymmPolynomial t (d - 1) i)) := by sorry
