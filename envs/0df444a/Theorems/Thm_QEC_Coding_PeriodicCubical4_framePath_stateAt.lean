-- Prove2me | Theorems.Thm_QEC_Coding_PeriodicCubical4_framePath_stateAt
-- name    : QEC.Coding.PeriodicCubical4.framePath_stateAt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T04:22:26.957929+00:00
-- url     : https://prove2.me/theorems/ffc412b1-23fe-44ba-893f-24f134088785
-- title:
--   Periodic Cubical4: frame Path state At
-- statement:
--   The Periodic Cubical4 construction uses the frame Path state At property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FourDimensionalToricCode/CoordinateSymmetry.lean#L576-L583
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FourDimensionalToricCode/CoordinateSymmetry.lean#L576-L583

import Definitions.Def_QEC_Coding_FourDimensionalToricCode_EnergyBarrierLowerBound
import Definitions.Def_QEC_Coding_FourDimensionalToricCode_MembraneSweep
import Definitions.Def_QEC_Coding_FourDimensionalToricCode_CoordinateSymmetry
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.PeriodicCubical4
open scoped Classical BigOperators
open PauliSymplectic StabilizerCode.LocalStabilizerHamiltonian
set_option maxHeartbeats 1000000

theorem QEC.Coding.PeriodicCubical4.framePath_stateAt {L : Nat} [NeZero L]
    (p : Plane) (gamma : PauliErrorPath (ι := Plaquette L)) (n : Nat) :
    (framePath p gamma).stateAt n = frameBinary p (gamma.stateAt n) := by sorry
