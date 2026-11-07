-- Prove2me | Theorems.Thm_QEC_Coding_PeriodicCubical4_half_le_pathHeight_of_primalProjectionEndpoint
-- name    : QEC.Coding.PeriodicCubical4.half_le_pathHeight_of_primalProjectionEndpoint
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T04:31:01.644541+00:00
-- url     : https://prove2.me/theorems/87acc9df-6ed7-4cf3-b7bd-d7a7672bb1cd
-- title:
--   Periodic Cubical4: half le path Height of primal Projection Endpoint
-- statement:
--   The #569 separator proof only needs an all-one primal endpoint projection.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FourDimensionalToricCode/CoordinateSymmetry.lean#L981-L1003
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FourDimensionalToricCode/CoordinateSymmetry.lean#L981-L1003

import Definitions.Def_QEC_Coding_FourDimensionalToricCode_EnergyBarrierLowerBound
import Definitions.Def_QEC_Coding_FourDimensionalToricCode_MembraneSweep
import Definitions.Def_QEC_Coding_FourDimensionalToricCode_CoordinateSymmetry
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.PeriodicCubical4
open scoped Classical BigOperators
open PauliSymplectic StabilizerCode.LocalStabilizerHamiltonian
set_option maxHeartbeats 1000000

theorem QEC.Coding.PeriodicCubical4.half_le_pathHeight_of_primalProjectionEndpoint
    {L : Nat} [NeZero L] [Fact (1 < L)]
    (gamma : PauliErrorPath (ι := Plaquette L))
    (hendpoint : primalSquareProjection gamma.endpoint.vector.zPart =
      fun _ _ => 1) :
    L / 2 ≤ (toricHamiltonian (L := L)).pathHeight gamma := by sorry
