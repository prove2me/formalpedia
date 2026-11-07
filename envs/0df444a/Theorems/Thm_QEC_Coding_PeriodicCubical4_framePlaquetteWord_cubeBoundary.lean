-- Prove2me | Theorems.Thm_QEC_Coding_PeriodicCubical4_framePlaquetteWord_cubeBoundary
-- name    : QEC.Coding.PeriodicCubical4.framePlaquetteWord_cubeBoundary
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T04:28:03.685709+00:00
-- url     : https://prove2.me/theorems/b1464270-68fb-4adc-990e-a992792c76c7
-- title:
--   Periodic Cubical4: frame Plaquette Word cube Boundary
-- statement:
--   Coordinate frames carry cube boundaries to cube boundaries.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FourDimensionalToricCode/CoordinateSymmetry.lean#L273-L280
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FourDimensionalToricCode/CoordinateSymmetry.lean#L273-L280

import Definitions.Def_QEC_Coding_FourDimensionalToricCode_EnergyBarrierLowerBound
import Definitions.Def_QEC_Coding_FourDimensionalToricCode_MembraneSweep
import Definitions.Def_QEC_Coding_FourDimensionalToricCode_CoordinateSymmetry
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.PeriodicCubical4
open scoped Classical BigOperators
open PauliSymplectic StabilizerCode.LocalStabilizerHamiltonian
set_option maxHeartbeats 1000000

theorem QEC.Coding.PeriodicCubical4.framePlaquetteWord_cubeBoundary {L : Nat} [NeZero L]
    (p : Plane) (c : Cube L) :
    framePlaquetteWord p (cubeBoundary c) =
      cubeBoundary (frameCube p c) := by sorry
