-- Prove2me | Theorems.Thm_QEC_Coding_PeriodicCubical4_pathHeight_primalCoordinateSweepPath_le
-- name    : QEC.Coding.PeriodicCubical4.pathHeight_primalCoordinateSweepPath_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T04:31:43.569999+00:00
-- url     : https://prove2.me/theorems/0a307325-6e17-417f-9a45-04e521eff0c3
-- title:
--   Periodic Cubical4: path Height primal Coordinate Sweep Path le
-- statement:
--   The Periodic Cubical4 construction uses the path Height primal Coordinate Sweep Path le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FourDimensionalToricCode/CoordinateSymmetry.lean#L1170-L1175
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FourDimensionalToricCode/CoordinateSymmetry.lean#L1170-L1175

import Definitions.Def_QEC_Coding_FourDimensionalToricCode_EnergyBarrierLowerBound
import Definitions.Def_QEC_Coding_FourDimensionalToricCode_MembraneSweep
import Definitions.Def_QEC_Coding_FourDimensionalToricCode_CoordinateSymmetry
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.PeriodicCubical4
open scoped Classical BigOperators
open PauliSymplectic StabilizerCode.LocalStabilizerHamiltonian
set_option maxHeartbeats 1000000

theorem QEC.Coding.PeriodicCubical4.pathHeight_primalCoordinateSweepPath_le
    {L : Nat} [NeZero L] [Fact (1 < L)] (p : Plane) :
    (toricHamiltonian (L := L)).pathHeight
      (primalCoordinateSweepPath (L := L) p) ≤ 64 * L := by sorry
