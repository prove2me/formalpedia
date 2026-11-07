-- Prove2me | Theorems.Thm_QEC_Coding_PeriodicCubical4_dualProjectionEndpoint_of_hasDualSectorEndpoint
-- name    : QEC.Coding.PeriodicCubical4.dualProjectionEndpoint_of_hasDualSectorEndpoint
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T04:30:36.417285+00:00
-- url     : https://prove2.me/theorems/c202b3f8-3059-4a00-958d-2ef0933a8c53
-- title:
--   Periodic Cubical4: dual Projection Endpoint of has Dual Sector Endpoint
-- statement:
--   The Periodic Cubical4 construction uses the dual Projection Endpoint of has Dual Sector Endpoint property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FourDimensionalToricCode/CoordinateSymmetry.lean#L967-L978
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FourDimensionalToricCode/CoordinateSymmetry.lean#L967-L978

import Definitions.Def_QEC_Coding_FourDimensionalToricCode_EnergyBarrierLowerBound
import Definitions.Def_QEC_Coding_FourDimensionalToricCode_MembraneSweep
import Definitions.Def_QEC_Coding_FourDimensionalToricCode_CoordinateSymmetry
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.PeriodicCubical4
open scoped Classical BigOperators
open PauliSymplectic StabilizerCode.LocalStabilizerHamiltonian
set_option maxHeartbeats 1000000

theorem QEC.Coding.PeriodicCubical4.dualProjectionEndpoint_of_hasDualSectorEndpoint
    {L : Nat} [NeZero L] [Fact (1 < L)]
    (gamma : PauliErrorPath (ι := Plaquette L)) (s : MembraneSector)
    (p : Plane) (hp : p ∈ s.1) (hendpoint : HasDualSectorEndpoint gamma s) :
    dualSquareProjection
      ((framePath p gamma).endpoint.vector.xPart) = fun _ _ => 1 := by sorry
