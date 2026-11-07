-- Prove2me | Theorems.Thm_QEC_Coding_PeriodicCubical4_dualSectorSweepPath_endpoint
-- name    : QEC.Coding.PeriodicCubical4.dualSectorSweepPath_endpoint
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T04:22:05.672235+00:00
-- url     : https://prove2.me/theorems/e9cd7289-f9c3-4c8a-a555-dc30fbab30af
-- title:
--   Periodic Cubical4: dual Sector Sweep Path endpoint
-- statement:
--   The Periodic Cubical4 construction uses the dual Sector Sweep Path endpoint property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FourDimensionalToricCode/CoordinateSymmetry.lean#L1162-L1168
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FourDimensionalToricCode/CoordinateSymmetry.lean#L1162-L1168

import Definitions.Def_QEC_Coding_FourDimensionalToricCode_EnergyBarrierLowerBound
import Definitions.Def_QEC_Coding_FourDimensionalToricCode_MembraneSweep
import Definitions.Def_QEC_Coding_FourDimensionalToricCode_CoordinateSymmetry
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.PeriodicCubical4
open scoped Classical BigOperators
open PauliSymplectic StabilizerCode.LocalStabilizerHamiltonian
set_option maxHeartbeats 1000000

theorem QEC.Coding.PeriodicCubical4.dualSectorSweepPath_endpoint
    {L : Nat} [NeZero L] [Fact (1 < L)] (s : MembraneSector) :
    (dualSectorSweepPath (L := L) s).endpoint =
      cssXCheck (dualSectorMembrane s) := by sorry
