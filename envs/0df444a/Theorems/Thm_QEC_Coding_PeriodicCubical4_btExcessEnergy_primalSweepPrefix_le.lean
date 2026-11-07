-- Prove2me | Theorems.Thm_QEC_Coding_PeriodicCubical4_btExcessEnergy_primalSweepPrefix_le
-- name    : QEC.Coding.PeriodicCubical4.btExcessEnergy_primalSweepPrefix_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T03:48:16.769213+00:00
-- url     : https://prove2.me/theorems/1baf4a16-8865-4736-b8c5-cc9ba7808e26
-- title:
--   Periodic Cubical4: bt Excess Energy primal Sweep Prefix le
-- statement:
--   BT-normalized excess energy of every primal geometric prefix is linear.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FourDimensionalToricCode/MembraneSweep.lean#L753-L760
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FourDimensionalToricCode/MembraneSweep.lean#L753-L760

import Definitions.Def_QEC_Coding_FourDimensionalToricCode_MembraneSyndrome
import Definitions.Def_QEC_Coding_Stabilizer_TwoDimensional_StripLogicalPath
import Definitions.Def_QEC_Coding_FourDimensionalToricCode_MembraneSweep
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.PeriodicCubical4
open scoped Classical BigOperators
open PauliSymplectic StabilizerCode.LocalStabilizerHamiltonian
variable {L : Nat} [NeZero L] [Fact (1 < L)]

theorem QEC.Coding.PeriodicCubical4.btExcessEnergy_primalSweepPrefix_le
    (z w : ZMod L) (n : Nat) (hn : n ≤ L * L) :
    (toricHamiltonian (L := L)).btExcessEnergy
        (primalMembraneError (primalSweepPrefix z w n)) ≤ 64 * L := by sorry
