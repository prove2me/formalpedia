-- Prove2me | Theorems.Thm_QEC_Coding_PeriodicCubical4_dualCoordinateMembrane_apply_eq_zero_of_plane_ne
-- name    : QEC.Coding.PeriodicCubical4.dualCoordinateMembrane_apply_eq_zero_of_plane_ne
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T04:31:44.148772+00:00
-- url     : https://prove2.me/theorems/5218e674-de92-425d-9d12-f7c4b6fc4486
-- title:
--   Periodic Cubical4: dual Coordinate Membrane apply eq zero of plane ne
-- statement:
--   The Periodic Cubical4 construction uses the dual Coordinate Membrane apply eq zero of plane ne property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FourDimensionalToricCode/CoordinateSymmetry.lean#L626-L633
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FourDimensionalToricCode/CoordinateSymmetry.lean#L626-L633

import Definitions.Def_QEC_Coding_FourDimensionalToricCode_EnergyBarrierLowerBound
import Definitions.Def_QEC_Coding_FourDimensionalToricCode_MembraneSweep
import Definitions.Def_QEC_Coding_FourDimensionalToricCode_CoordinateSymmetry
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.PeriodicCubical4
open scoped Classical BigOperators
open PauliSymplectic StabilizerCode.LocalStabilizerHamiltonian
set_option maxHeartbeats 1000000

theorem QEC.Coding.PeriodicCubical4.dualCoordinateMembrane_apply_eq_zero_of_plane_ne
    {L : Nat} [NeZero L] (p : Plane) (u v : ZMod L)
    (c : Coord L) (q : Plane) (hqp : q ≠ p) :
    dualCoordinateMembrane p u v (c, q) = 0 := by sorry
