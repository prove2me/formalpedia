-- Prove2me | Theorems.Thm_QEC_Coding_PeriodicCubical4_endpoint_appendDualSweepList
-- name    : QEC.Coding.PeriodicCubical4.endpoint_appendDualSweepList
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T04:31:28.443759+00:00
-- url     : https://prove2.me/theorems/88c9c2d2-5579-4ac3-9686-b93a9acfb8ff
-- title:
--   Periodic Cubical4: endpoint append Dual Sweep List
-- statement:
--   The Periodic Cubical4 construction uses the endpoint append Dual Sweep List property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FourDimensionalToricCode/CoordinateSymmetry.lean#L1129-L1138
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FourDimensionalToricCode/CoordinateSymmetry.lean#L1129-L1138

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

theorem QEC.Coding.PeriodicCubical4.endpoint_appendDualSweepList
    {L : Nat} [NeZero L] [Fact (1 < L)] (planes : List Plane) :
    (appendMembranePaths
      (planes.map (dualCoordinateSweepPath (L := L)))).endpoint =
      cssXCheck ((planes.map
        (fun p => dualCoordinateMembrane (L := L) p 0 0)).sum) := by sorry
