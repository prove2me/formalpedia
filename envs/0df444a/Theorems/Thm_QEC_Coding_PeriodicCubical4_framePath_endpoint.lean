-- Prove2me | Theorems.Thm_QEC_Coding_PeriodicCubical4_framePath_endpoint
-- name    : QEC.Coding.PeriodicCubical4.framePath_endpoint
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T04:22:49.071242+00:00
-- url     : https://prove2.me/theorems/f0ab1fad-b8f3-4c2c-a5d5-1b69d7d3878d
-- title:
--   Periodic Cubical4: frame Path endpoint
-- statement:
--   The Periodic Cubical4 construction uses the frame Path endpoint property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FourDimensionalToricCode/CoordinateSymmetry.lean#L571-L574
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FourDimensionalToricCode/CoordinateSymmetry.lean#L571-L574

import Definitions.Def_QEC_Coding_FourDimensionalToricCode_EnergyBarrierLowerBound
import Definitions.Def_QEC_Coding_FourDimensionalToricCode_MembraneSweep
import Definitions.Def_QEC_Coding_FourDimensionalToricCode_CoordinateSymmetry
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.PeriodicCubical4
open scoped Classical BigOperators
open PauliSymplectic StabilizerCode.LocalStabilizerHamiltonian
set_option maxHeartbeats 1000000

theorem QEC.Coding.PeriodicCubical4.framePath_endpoint {L : Nat} [NeZero L]
    (p : Plane) (gamma : PauliErrorPath (ι := Plaquette L)) :
    (framePath p gamma).endpoint = frameBinary p gamma.endpoint := by sorry
