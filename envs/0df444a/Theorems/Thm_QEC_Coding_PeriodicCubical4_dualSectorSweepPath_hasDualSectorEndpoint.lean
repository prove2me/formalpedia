-- Prove2me | Theorems.Thm_QEC_Coding_PeriodicCubical4_dualSectorSweepPath_hasDualSectorEndpoint
-- name    : QEC.Coding.PeriodicCubical4.dualSectorSweepPath_hasDualSectorEndpoint
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T04:32:26.940444+00:00
-- url     : https://prove2.me/theorems/e4df9705-681e-40a3-8cea-a16ecbad02bd
-- title:
--   Periodic Cubical4: dual Sector Sweep Path has Dual Sector Endpoint
-- statement:
--   The Periodic Cubical4 construction uses the dual Sector Sweep Path has Dual Sector Endpoint property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FourDimensionalToricCode/CoordinateSymmetry.lean#L1274-L1278
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FourDimensionalToricCode/CoordinateSymmetry.lean#L1274-L1278

import Definitions.Def_QEC_Coding_FourDimensionalToricCode_EnergyBarrierLowerBound
import Definitions.Def_QEC_Coding_FourDimensionalToricCode_MembraneSweep
import Definitions.Def_QEC_Coding_FourDimensionalToricCode_CoordinateSymmetry
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.PeriodicCubical4
open scoped Classical BigOperators
open PauliSymplectic StabilizerCode.LocalStabilizerHamiltonian
set_option maxHeartbeats 1000000

theorem QEC.Coding.PeriodicCubical4.dualSectorSweepPath_hasDualSectorEndpoint
    {L : Nat} [NeZero L] [Fact (1 < L)] (s : MembraneSector) :
    HasDualSectorEndpoint (dualSectorSweepPath (L := L) s) s := by sorry
