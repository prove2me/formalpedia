-- Prove2me | Theorems.Thm_QEC_Coding_PeriodicCubical4_btExcessEnergy_dualSweepPrefix_le
-- name    : QEC.Coding.PeriodicCubical4.btExcessEnergy_dualSweepPrefix_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T03:48:25.359199+00:00
-- url     : https://prove2.me/theorems/c1bb4ac1-3fbb-4bc4-8a09-80eee0f47d28
-- title:
--   Periodic Cubical4: bt Excess Energy dual Sweep Prefix le
-- statement:
--   BT-normalized excess energy of every dual geometric prefix is linear.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FourDimensionalToricCode/MembraneSweep.lean#L763-L770
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FourDimensionalToricCode/MembraneSweep.lean#L763-L770

import Definitions.Def_QEC_Coding_FourDimensionalToricCode_MembraneSyndrome
import Definitions.Def_QEC_Coding_Stabilizer_TwoDimensional_StripLogicalPath
import Definitions.Def_QEC_Coding_FourDimensionalToricCode_MembraneSweep
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.PeriodicCubical4
open scoped Classical BigOperators
open PauliSymplectic StabilizerCode.LocalStabilizerHamiltonian
variable {L : Nat} [NeZero L] [Fact (1 < L)]

theorem QEC.Coding.PeriodicCubical4.btExcessEnergy_dualSweepPrefix_le
    (x y : ZMod L) (n : Nat) (hn : n ≤ L * L) :
    (toricHamiltonian (L := L)).btExcessEnergy
        (dualMembraneError (dualSweepPrefix x y n)) ≤ 64 * L := by sorry
