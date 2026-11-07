-- Prove2me | Theorems.Thm_QEC_Coding_PeriodicCubical4_primalCoordinateSweepPath_endpoint
-- name    : QEC.Coding.PeriodicCubical4.primalCoordinateSweepPath_endpoint
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T04:21:44.395328+00:00
-- url     : https://prove2.me/theorems/1434b9fa-0d1d-4139-b696-de5a2c3953b5
-- title:
--   Periodic Cubical4: primal Coordinate Sweep Path endpoint
-- statement:
--   The Periodic Cubical4 construction uses the primal Coordinate Sweep Path endpoint property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FourDimensionalToricCode/CoordinateSymmetry.lean#L1104-L1109
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FourDimensionalToricCode/CoordinateSymmetry.lean#L1104-L1109

import Definitions.Def_QEC_Coding_FourDimensionalToricCode_EnergyBarrierLowerBound
import Definitions.Def_QEC_Coding_FourDimensionalToricCode_MembraneSweep
import Definitions.Def_QEC_Coding_FourDimensionalToricCode_CoordinateSymmetry
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.PeriodicCubical4
open scoped Classical BigOperators
open PauliSymplectic StabilizerCode.LocalStabilizerHamiltonian
set_option maxHeartbeats 1000000

theorem QEC.Coding.PeriodicCubical4.primalCoordinateSweepPath_endpoint
    {L : Nat} [NeZero L] [Fact (1 < L)] (p : Plane) :
    (primalCoordinateSweepPath (L := L) p).endpoint =
      cssZCheck (primalCoordinateMembrane p 0 0) := by sorry
