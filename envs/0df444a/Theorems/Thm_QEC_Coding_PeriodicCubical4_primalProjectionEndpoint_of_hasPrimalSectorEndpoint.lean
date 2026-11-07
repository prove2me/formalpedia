-- Prove2me | Theorems.Thm_QEC_Coding_PeriodicCubical4_primalProjectionEndpoint_of_hasPrimalSectorEndpoint
-- name    : QEC.Coding.PeriodicCubical4.primalProjectionEndpoint_of_hasPrimalSectorEndpoint
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T04:31:07.233316+00:00
-- url     : https://prove2.me/theorems/f61de470-1ec9-49ae-8e2a-326ca02f0216
-- title:
--   Periodic Cubical4: primal Projection Endpoint of has Primal Sector Endpoint
-- statement:
--   The Periodic Cubical4 construction uses the primal Projection Endpoint of has Primal Sector Endpoint property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FourDimensionalToricCode/CoordinateSymmetry.lean#L954-L965
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FourDimensionalToricCode/CoordinateSymmetry.lean#L954-L965

import Definitions.Def_QEC_Coding_FourDimensionalToricCode_EnergyBarrierLowerBound
import Definitions.Def_QEC_Coding_FourDimensionalToricCode_MembraneSweep
import Definitions.Def_QEC_Coding_FourDimensionalToricCode_CoordinateSymmetry
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.PeriodicCubical4
open scoped Classical BigOperators
open PauliSymplectic StabilizerCode.LocalStabilizerHamiltonian
set_option maxHeartbeats 1000000

theorem QEC.Coding.PeriodicCubical4.primalProjectionEndpoint_of_hasPrimalSectorEndpoint
    {L : Nat} [NeZero L] [Fact (1 < L)]
    (gamma : PauliErrorPath (ι := Plaquette L)) (s : MembraneSector)
    (p : Plane) (hp : p ∈ s.1) (hendpoint : HasPrimalSectorEndpoint gamma s) :
    primalSquareProjection
      ((framePath p gamma).endpoint.vector.zPart) = fun _ _ => 1 := by sorry
