-- Prove2me | Theorems.Thm_QEC_Coding_PeriodicCubical4_pathHeight_dualCoordinateSweepPath_le
-- name    : QEC.Coding.PeriodicCubical4.pathHeight_dualCoordinateSweepPath_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T04:32:17.187822+00:00
-- url     : https://prove2.me/theorems/d388155b-d821-4f87-8028-ec52e810e023
-- title:
--   Periodic Cubical4: path Height dual Coordinate Sweep Path le
-- statement:
--   The Periodic Cubical4 construction uses the path Height dual Coordinate Sweep Path le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FourDimensionalToricCode/CoordinateSymmetry.lean#L1177-L1182
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FourDimensionalToricCode/CoordinateSymmetry.lean#L1177-L1182

import Definitions.Def_QEC_Coding_FourDimensionalToricCode_EnergyBarrierLowerBound
import Definitions.Def_QEC_Coding_FourDimensionalToricCode_MembraneSweep
import Definitions.Def_QEC_Coding_FourDimensionalToricCode_CoordinateSymmetry
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.PeriodicCubical4
open scoped Classical BigOperators
open PauliSymplectic StabilizerCode.LocalStabilizerHamiltonian
set_option maxHeartbeats 1000000

theorem QEC.Coding.PeriodicCubical4.pathHeight_dualCoordinateSweepPath_le
    {L : Nat} [NeZero L] [Fact (1 < L)] (p : Plane) :
    (toricHamiltonian (L := L)).pathHeight
      (dualCoordinateSweepPath (L := L) p) ≤ 64 * L := by sorry
