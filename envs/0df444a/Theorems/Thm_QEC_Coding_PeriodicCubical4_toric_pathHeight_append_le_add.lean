-- Prove2me | Theorems.Thm_QEC_Coding_PeriodicCubical4_toric_pathHeight_append_le_add
-- name    : QEC.Coding.PeriodicCubical4.toric_pathHeight_append_le_add
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T04:25:30.061635+00:00
-- url     : https://prove2.me/theorems/3df821d3-4ad1-4ef0-b8f6-613b592d5221
-- title:
--   Periodic Cubical4: toric path Height append le add
-- statement:
--   Path height is subadditive when two actual single-qubit paths are concatenated.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FourDimensionalToricCode/CoordinateSymmetry.lean#L1055-L1086
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FourDimensionalToricCode/CoordinateSymmetry.lean#L1055-L1086

import Definitions.Def_QEC_Coding_FourDimensionalToricCode_EnergyBarrierLowerBound
import Definitions.Def_QEC_Coding_FourDimensionalToricCode_MembraneSweep
import Definitions.Def_QEC_Coding_FourDimensionalToricCode_CoordinateSymmetry
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.PeriodicCubical4
open scoped Classical BigOperators
open PauliSymplectic StabilizerCode.LocalStabilizerHamiltonian
set_option maxHeartbeats 1000000

theorem QEC.Coding.PeriodicCubical4.toric_pathHeight_append_le_add {L : Nat} [NeZero L] [Fact (1 < L)]
    (gamma delta : PauliErrorPath (ι := Plaquette L)) :
    (toricHamiltonian (L := L)).pathHeight (gamma.append delta) ≤
      (toricHamiltonian (L := L)).pathHeight gamma +
        (toricHamiltonian (L := L)).pathHeight delta := by sorry
