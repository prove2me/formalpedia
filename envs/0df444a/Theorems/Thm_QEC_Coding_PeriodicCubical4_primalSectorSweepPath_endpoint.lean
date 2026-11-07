-- Prove2me | Theorems.Thm_QEC_Coding_PeriodicCubical4_primalSectorSweepPath_endpoint
-- name    : QEC.Coding.PeriodicCubical4.primalSectorSweepPath_endpoint
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T04:21:54.001944+00:00
-- url     : https://prove2.me/theorems/a52b4070-8846-4698-8485-9a17eb247465
-- title:
--   Periodic Cubical4: primal Sector Sweep Path endpoint
-- statement:
--   The Periodic Cubical4 construction uses the primal Sector Sweep Path endpoint property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FourDimensionalToricCode/CoordinateSymmetry.lean#L1154-L1160
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FourDimensionalToricCode/CoordinateSymmetry.lean#L1154-L1160

import Definitions.Def_QEC_Coding_FourDimensionalToricCode_EnergyBarrierLowerBound
import Definitions.Def_QEC_Coding_FourDimensionalToricCode_MembraneSweep
import Definitions.Def_QEC_Coding_FourDimensionalToricCode_CoordinateSymmetry
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.PeriodicCubical4
open scoped Classical BigOperators
open PauliSymplectic StabilizerCode.LocalStabilizerHamiltonian
set_option maxHeartbeats 1000000

theorem QEC.Coding.PeriodicCubical4.primalSectorSweepPath_endpoint
    {L : Nat} [NeZero L] [Fact (1 < L)] (s : MembraneSector) :
    (primalSectorSweepPath (L := L) s).endpoint =
      cssZCheck (primalSectorMembrane s) := by sorry
