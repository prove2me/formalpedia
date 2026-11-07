-- Prove2me | Theorems.Thm_QEC_Coding_PeriodicCubical4_pathHeight_dualMembraneSweepPath_le
-- name    : QEC.Coding.PeriodicCubical4.pathHeight_dualMembraneSweepPath_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T03:52:47.552466+00:00
-- url     : https://prove2.me/theorems/38bc688d-d27e-4689-a6c0-8a2817ad0094
-- title:
--   Periodic Cubical4: path Height dual Membrane Sweep Path le
-- statement:
--   The explicit dual membrane sweep has a linear BT energy height.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FourDimensionalToricCode/MembraneSweep.lean#L1108-L1115
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FourDimensionalToricCode/MembraneSweep.lean#L1108-L1115

import Definitions.Def_QEC_Coding_FourDimensionalToricCode_MembraneSyndrome
import Definitions.Def_QEC_Coding_Stabilizer_TwoDimensional_StripLogicalPath
import Definitions.Def_QEC_Coding_FourDimensionalToricCode_MembraneSweep
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.PeriodicCubical4
open scoped Classical BigOperators
open PauliSymplectic StabilizerCode.LocalStabilizerHamiltonian
variable {L : Nat} [NeZero L] [Fact (1 < L)]

theorem QEC.Coding.PeriodicCubical4.pathHeight_dualMembraneSweepPath_le (x y : ZMod L) :
    (toricHamiltonian (L := L)).pathHeight
        (dualMembraneSweepPath x y) ≤ 64 * L := by sorry
