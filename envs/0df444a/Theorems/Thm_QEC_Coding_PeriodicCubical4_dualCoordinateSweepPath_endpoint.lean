-- Prove2me | Theorems.Thm_QEC_Coding_PeriodicCubical4_dualCoordinateSweepPath_endpoint
-- name    : QEC.Coding.PeriodicCubical4.dualCoordinateSweepPath_endpoint
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T04:21:53.844789+00:00
-- url     : https://prove2.me/theorems/a1d99752-b89c-48ef-9b34-ed364af48fa0
-- title:
--   Periodic Cubical4: dual Coordinate Sweep Path endpoint
-- statement:
--   The Periodic Cubical4 construction uses the dual Coordinate Sweep Path endpoint property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FourDimensionalToricCode/CoordinateSymmetry.lean#L1111-L1116
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FourDimensionalToricCode/CoordinateSymmetry.lean#L1111-L1116

import Definitions.Def_QEC_Coding_FourDimensionalToricCode_EnergyBarrierLowerBound
import Definitions.Def_QEC_Coding_FourDimensionalToricCode_MembraneSweep
import Definitions.Def_QEC_Coding_FourDimensionalToricCode_CoordinateSymmetry
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.PeriodicCubical4
open scoped Classical BigOperators
open PauliSymplectic StabilizerCode.LocalStabilizerHamiltonian
set_option maxHeartbeats 1000000

theorem QEC.Coding.PeriodicCubical4.dualCoordinateSweepPath_endpoint
    {L : Nat} [NeZero L] [Fact (1 < L)] (p : Plane) :
    (dualCoordinateSweepPath (L := L) p).endpoint =
      cssXCheck (dualCoordinateMembrane p 0 0) := by sorry
