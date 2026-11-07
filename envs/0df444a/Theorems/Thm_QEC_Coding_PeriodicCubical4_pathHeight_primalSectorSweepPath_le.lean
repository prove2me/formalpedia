-- Prove2me | Theorems.Thm_QEC_Coding_PeriodicCubical4_pathHeight_primalSectorSweepPath_le
-- name    : QEC.Coding.PeriodicCubical4.pathHeight_primalSectorSweepPath_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T04:32:59.394063+00:00
-- url     : https://prove2.me/theorems/acaaa519-36e0-423b-a3b5-5869a77c3b3a
-- title:
--   Periodic Cubical4: path Height primal Sector Sweep Path le
-- statement:
--   Every nonzero primal sector has an explicit sweep of height at most `384 L`.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FourDimensionalToricCode/CoordinateSymmetry.lean#L1243-L1253
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FourDimensionalToricCode/CoordinateSymmetry.lean#L1243-L1253

import Definitions.Def_QEC_Coding_FourDimensionalToricCode_EnergyBarrierLowerBound
import Definitions.Def_QEC_Coding_FourDimensionalToricCode_MembraneSweep
import Definitions.Def_QEC_Coding_FourDimensionalToricCode_CoordinateSymmetry
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.PeriodicCubical4
open scoped Classical BigOperators
open PauliSymplectic StabilizerCode.LocalStabilizerHamiltonian
set_option maxHeartbeats 1000000

theorem QEC.Coding.PeriodicCubical4.pathHeight_primalSectorSweepPath_le
    {L : Nat} [NeZero L] [Fact (1 < L)] (s : MembraneSector) :
    (toricHamiltonian (L := L)).pathHeight
      (primalSectorSweepPath (L := L) s) ≤ 384 * L := by sorry
