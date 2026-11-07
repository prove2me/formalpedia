-- Prove2me | Theorems.Thm_QEC_Coding_PeriodicCubical4_endpoint_appendPrimalSweepList
-- name    : QEC.Coding.PeriodicCubical4.endpoint_appendPrimalSweepList
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T04:31:16.490201+00:00
-- url     : https://prove2.me/theorems/899284b3-4f97-4566-aecc-dead50dabc53
-- title:
--   Periodic Cubical4: endpoint append Primal Sweep List
-- statement:
--   The Periodic Cubical4 construction uses the endpoint append Primal Sweep List property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FourDimensionalToricCode/CoordinateSymmetry.lean#L1118-L1127
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FourDimensionalToricCode/CoordinateSymmetry.lean#L1118-L1127

import Definitions.Def_QEC_Coding_FourDimensionalToricCode_EnergyBarrierLowerBound
import Definitions.Def_QEC_Coding_FourDimensionalToricCode_MembraneSweep
import Definitions.Def_QEC_Coding_FourDimensionalToricCode_CoordinateSymmetry
import Theorems.Thm_QEC_Semantics_QuditSubsystem_ScalarCompression_sum

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.PeriodicCubical4
open scoped Classical BigOperators
open PauliSymplectic StabilizerCode.LocalStabilizerHamiltonian
set_option maxHeartbeats 1000000

theorem QEC.Coding.PeriodicCubical4.endpoint_appendPrimalSweepList
    {L : Nat} [NeZero L] [Fact (1 < L)] (planes : List Plane) :
    (appendMembranePaths
      (planes.map (primalCoordinateSweepPath (L := L)))).endpoint =
      cssZCheck ((planes.map
        (fun p => primalCoordinateMembrane (L := L) p 0 0)).sum) := by sorry
