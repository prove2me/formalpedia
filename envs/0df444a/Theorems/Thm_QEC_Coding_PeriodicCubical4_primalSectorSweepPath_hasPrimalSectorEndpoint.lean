-- Prove2me | Theorems.Thm_QEC_Coding_PeriodicCubical4_primalSectorSweepPath_hasPrimalSectorEndpoint
-- name    : QEC.Coding.PeriodicCubical4.primalSectorSweepPath_hasPrimalSectorEndpoint
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T04:32:27.490734+00:00
-- url     : https://prove2.me/theorems/e52bcb1e-8ed1-4fce-8b85-bd89bc717071
-- title:
--   Periodic Cubical4: primal Sector Sweep Path has Primal Sector Endpoint
-- statement:
--   The Periodic Cubical4 construction uses the primal Sector Sweep Path has Primal Sector Endpoint property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FourDimensionalToricCode/CoordinateSymmetry.lean#L1268-L1272
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FourDimensionalToricCode/CoordinateSymmetry.lean#L1268-L1272

import Definitions.Def_QEC_Coding_FourDimensionalToricCode_EnergyBarrierLowerBound
import Definitions.Def_QEC_Coding_FourDimensionalToricCode_MembraneSweep
import Definitions.Def_QEC_Coding_FourDimensionalToricCode_CoordinateSymmetry
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.PeriodicCubical4
open scoped Classical BigOperators
open PauliSymplectic StabilizerCode.LocalStabilizerHamiltonian
set_option maxHeartbeats 1000000

theorem QEC.Coding.PeriodicCubical4.primalSectorSweepPath_hasPrimalSectorEndpoint
    {L : Nat} [NeZero L] [Fact (1 < L)] (s : MembraneSector) :
    HasPrimalSectorEndpoint (primalSectorSweepPath (L := L) s) s := by sorry
