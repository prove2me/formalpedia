-- Prove2me | Theorems.Thm_QEC_Coding_PeriodicCubical4_pathHeight_primalMembraneSweepPath_le
-- name    : QEC.Coding.PeriodicCubical4.pathHeight_primalMembraneSweepPath_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T03:52:09.637202+00:00
-- url     : https://prove2.me/theorems/bf1fe226-501b-4f72-9cca-42d8ed53ae79
-- title:
--   Periodic Cubical4: path Height primal Membrane Sweep Path le
-- statement:
--   The explicit primal membrane sweep has a linear BT energy height.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FourDimensionalToricCode/MembraneSweep.lean#L1098-L1105
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FourDimensionalToricCode/MembraneSweep.lean#L1098-L1105

import Definitions.Def_QEC_Coding_FourDimensionalToricCode_MembraneSyndrome
import Definitions.Def_QEC_Coding_Stabilizer_TwoDimensional_StripLogicalPath
import Definitions.Def_QEC_Coding_FourDimensionalToricCode_MembraneSweep
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.PeriodicCubical4
open scoped Classical BigOperators
open PauliSymplectic StabilizerCode.LocalStabilizerHamiltonian
variable {L : Nat} [NeZero L] [Fact (1 < L)]

theorem QEC.Coding.PeriodicCubical4.pathHeight_primalMembraneSweepPath_le (z w : ZMod L) :
    (toricHamiltonian (L := L)).pathHeight
        (primalMembraneSweepPath z w) ≤ 64 * L := by sorry
