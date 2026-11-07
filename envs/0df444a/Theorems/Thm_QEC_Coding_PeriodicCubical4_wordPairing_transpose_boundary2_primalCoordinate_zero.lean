-- Prove2me | Theorems.Thm_QEC_Coding_PeriodicCubical4_wordPairing_transpose_boundary2_primalCoordinate_zero
-- name    : QEC.Coding.PeriodicCubical4.wordPairing_transpose_boundary2_primalCoordinate_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T04:24:52.319661+00:00
-- url     : https://prove2.me/theorems/2a4608ce-e7db-444f-aff8-fcba6b8b6206
-- title:
--   Periodic Cubical4: word Pairing transpose boundary2 primal Coordinate zero
-- statement:
--   Every coordinate primal membrane annihilates dual stabilizer coboundaries.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FourDimensionalToricCode/CoordinateSymmetry.lean#L733-L751
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FourDimensionalToricCode/CoordinateSymmetry.lean#L733-L751

import Definitions.Def_QEC_Coding_FourDimensionalToricCode_EnergyBarrierLowerBound
import Definitions.Def_QEC_Coding_FourDimensionalToricCode_MembraneSweep
import Definitions.Def_QEC_Coding_FourDimensionalToricCode_CoordinateSymmetry
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.PeriodicCubical4
open scoped Classical BigOperators
open PauliSymplectic StabilizerCode.LocalStabilizerHamiltonian
set_option maxHeartbeats 1000000

theorem QEC.Coding.PeriodicCubical4.wordPairing_transpose_boundary2_primalCoordinate_zero
    {L : Nat} [NeZero L] (p : Plane) (a b : ZMod L)
    (e : Word (ZMod 2) (Link L)) :
    wordPairing (wordLinearMapTranspose boundary2 e)
      (primalCoordinateMembrane p a b) = 0 := by sorry
