-- Prove2me | Theorems.Thm_QEC_Coding_PeriodicCubical4_half_le_pathHeight_of_dualProjectionEndpoint
-- name    : QEC.Coding.PeriodicCubical4.half_le_pathHeight_of_dualProjectionEndpoint
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T04:30:37.744191+00:00
-- url     : https://prove2.me/theorems/090939e4-753b-4ac6-b04c-40e3cc01ff5e
-- title:
--   Periodic Cubical4: half le path Height of dual Projection Endpoint
-- statement:
--   The #569 separator proof only needs an all-one dual endpoint projection.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FourDimensionalToricCode/CoordinateSymmetry.lean#L1006-L1028
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FourDimensionalToricCode/CoordinateSymmetry.lean#L1006-L1028

import Definitions.Def_QEC_Coding_FourDimensionalToricCode_EnergyBarrierLowerBound
import Definitions.Def_QEC_Coding_FourDimensionalToricCode_MembraneSweep
import Definitions.Def_QEC_Coding_FourDimensionalToricCode_CoordinateSymmetry
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.PeriodicCubical4
open scoped Classical BigOperators
open PauliSymplectic StabilizerCode.LocalStabilizerHamiltonian
set_option maxHeartbeats 1000000

theorem QEC.Coding.PeriodicCubical4.half_le_pathHeight_of_dualProjectionEndpoint
    {L : Nat} [NeZero L] [Fact (1 < L)]
    (gamma : PauliErrorPath (ι := Plaquette L))
    (hendpoint : dualSquareProjection gamma.endpoint.vector.xPart =
      fun _ _ => 1) :
    L / 2 ≤ (toricHamiltonian (L := L)).pathHeight gamma := by sorry
