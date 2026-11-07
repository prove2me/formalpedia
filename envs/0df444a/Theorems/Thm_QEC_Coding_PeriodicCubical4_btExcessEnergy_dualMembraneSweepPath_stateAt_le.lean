-- Prove2me | Theorems.Thm_QEC_Coding_PeriodicCubical4_btExcessEnergy_dualMembraneSweepPath_stateAt_le
-- name    : QEC.Coding.PeriodicCubical4.btExcessEnergy_dualMembraneSweepPath_stateAt_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T03:54:57.557074+00:00
-- url     : https://prove2.me/theorems/0cbd8654-25fa-497a-9394-cb9627dd5f89
-- title:
--   Periodic Cubical4: bt Excess Energy dual Membrane Sweep Path state At le
-- statement:
--   The Periodic Cubical4 construction uses the bt Excess Energy dual Membrane Sweep Path state At le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FourDimensionalToricCode/MembraneSweep.lean#L1062-L1095
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FourDimensionalToricCode/MembraneSweep.lean#L1062-L1095

import Definitions.Def_QEC_Coding_FourDimensionalToricCode_MembraneSyndrome
import Definitions.Def_QEC_Coding_Stabilizer_TwoDimensional_StripLogicalPath
import Definitions.Def_QEC_Coding_FourDimensionalToricCode_MembraneSweep
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.PeriodicCubical4
open scoped Classical BigOperators
open PauliSymplectic StabilizerCode.LocalStabilizerHamiltonian
variable {L : Nat} [NeZero L] [Fact (1 < L)]

theorem QEC.Coding.PeriodicCubical4.btExcessEnergy_dualMembraneSweepPath_stateAt_le
    (x y : ZMod L) (n : Nat)
    (hn : n ≤ (dualMembraneSweepPath x y).increments.length) :
    (toricHamiltonian (L := L)).btExcessEnergy
        ((dualMembraneSweepPath x y).stateAt n) ≤ 64 * L := by sorry
