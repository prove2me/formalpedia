-- Prove2me | Theorems.Thm_QEC_Coding_PeriodicCubical4_framePath_increments
-- name    : QEC.Coding.PeriodicCubical4.framePath_increments
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T04:21:44.487955+00:00
-- url     : https://prove2.me/theorems/cf7ca5ea-f9a1-41d5-a2a3-8b17d275df1d
-- title:
--   Periodic Cubical4: frame Path increments
-- statement:
--   The Periodic Cubical4 construction uses the frame Path increments property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FourDimensionalToricCode/CoordinateSymmetry.lean#L546-L548
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FourDimensionalToricCode/CoordinateSymmetry.lean#L546-L548

import Definitions.Def_QEC_Coding_FourDimensionalToricCode_EnergyBarrierLowerBound
import Definitions.Def_QEC_Coding_FourDimensionalToricCode_MembraneSweep
import Definitions.Def_QEC_Coding_FourDimensionalToricCode_CoordinateSymmetry
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.PeriodicCubical4
open scoped Classical BigOperators
open PauliSymplectic StabilizerCode.LocalStabilizerHamiltonian
set_option maxHeartbeats 1000000

theorem QEC.Coding.PeriodicCubical4.framePath_increments {L : Nat} [NeZero L]
    (p : Plane) (gamma : PauliErrorPath (ι := Plaquette L)) :
    (framePath p gamma).increments = gamma.increments.map (frameBinary p) := by sorry

attribute [defeq] QEC.Coding.PeriodicCubical4.framePath_increments
