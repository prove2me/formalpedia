-- Prove2me | Theorems.Thm_QEC_Coding_PeriodicCubical4_wordPairing_dualCoordinate_boundary3_zero
-- name    : QEC.Coding.PeriodicCubical4.wordPairing_dualCoordinate_boundary3_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T04:25:30.754199+00:00
-- url     : https://prove2.me/theorems/302ad723-c572-42bf-82f4-4c53b475904f
-- title:
--   Periodic Cubical4: word Pairing dual Coordinate boundary3 zero
-- statement:
--   Every coordinate dual membrane annihilates primal stabilizer boundaries.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FourDimensionalToricCode/CoordinateSymmetry.lean#L723-L730
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FourDimensionalToricCode/CoordinateSymmetry.lean#L723-L730

import Definitions.Def_QEC_Coding_FourDimensionalToricCode_EnergyBarrierLowerBound
import Definitions.Def_QEC_Coding_FourDimensionalToricCode_MembraneSweep
import Definitions.Def_QEC_Coding_FourDimensionalToricCode_CoordinateSymmetry
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.PeriodicCubical4
open scoped Classical BigOperators
open PauliSymplectic StabilizerCode.LocalStabilizerHamiltonian
set_option maxHeartbeats 1000000

theorem QEC.Coding.PeriodicCubical4.wordPairing_dualCoordinate_boundary3_zero
    {L : Nat} [NeZero L] (p : Plane) (a b : ZMod L)
    (c : Word (ZMod 2) (Cube L)) :
    wordPairing (dualCoordinateMembrane p a b) (boundary3 c) = 0 := by sorry
