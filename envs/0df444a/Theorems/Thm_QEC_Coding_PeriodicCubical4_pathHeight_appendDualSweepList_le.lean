-- Prove2me | Theorems.Thm_QEC_Coding_PeriodicCubical4_pathHeight_appendDualSweepList_le
-- name    : QEC.Coding.PeriodicCubical4.pathHeight_appendDualSweepList_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T04:32:12.055912+00:00
-- url     : https://prove2.me/theorems/3f0f28b2-a041-45a6-868e-0c1239779e44
-- title:
--   Periodic Cubical4: path Height append Dual Sweep List le
-- statement:
--   The Periodic Cubical4 construction uses the path Height append Dual Sweep List le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FourDimensionalToricCode/CoordinateSymmetry.lean#L1210-L1234
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FourDimensionalToricCode/CoordinateSymmetry.lean#L1210-L1234

import Definitions.Def_QEC_Coding_FourDimensionalToricCode_EnergyBarrierLowerBound
import Definitions.Def_QEC_Coding_FourDimensionalToricCode_MembraneSweep
import Definitions.Def_QEC_Coding_FourDimensionalToricCode_CoordinateSymmetry
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.PeriodicCubical4
open scoped Classical BigOperators
open PauliSymplectic StabilizerCode.LocalStabilizerHamiltonian
set_option maxHeartbeats 1000000

theorem QEC.Coding.PeriodicCubical4.pathHeight_appendDualSweepList_le
    {L : Nat} [NeZero L] [Fact (1 < L)] (planes : List Plane) :
    (toricHamiltonian (L := L)).pathHeight
      (appendMembranePaths
        (planes.map (dualCoordinateSweepPath (L := L)))) ≤
      planes.length * (64 * L) := by sorry
