-- Prove2me | Theorems.Thm_QEC_Coding_PeriodicCubical4_pathHeight_dualSectorSweepPath_le
-- name    : QEC.Coding.PeriodicCubical4.pathHeight_dualSectorSweepPath_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T04:32:16.468817+00:00
-- url     : https://prove2.me/theorems/e228223a-4145-4871-be27-599efa907bab
-- title:
--   Periodic Cubical4: path Height dual Sector Sweep Path le
-- statement:
--   Every nonzero dual sector has an explicit sweep of height at most `384 L`.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FourDimensionalToricCode/CoordinateSymmetry.lean#L1256-L1266
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FourDimensionalToricCode/CoordinateSymmetry.lean#L1256-L1266

import Definitions.Def_QEC_Coding_FourDimensionalToricCode_EnergyBarrierLowerBound
import Definitions.Def_QEC_Coding_FourDimensionalToricCode_MembraneSweep
import Definitions.Def_QEC_Coding_FourDimensionalToricCode_CoordinateSymmetry
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.PeriodicCubical4
open scoped Classical BigOperators
open PauliSymplectic StabilizerCode.LocalStabilizerHamiltonian
set_option maxHeartbeats 1000000

theorem QEC.Coding.PeriodicCubical4.pathHeight_dualSectorSweepPath_le
    {L : Nat} [NeZero L] [Fact (1 < L)] (s : MembraneSector) :
    (toricHamiltonian (L := L)).pathHeight
      (dualSectorSweepPath (L := L) s) ≤ 384 * L := by sorry
