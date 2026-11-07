-- Prove2me | Theorems.Thm_QEC_Coding_PeriodicCubical4_take_dualSweepOrder_of_le
-- name    : QEC.Coding.PeriodicCubical4.take_dualSweepOrder_of_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T03:52:21.527859+00:00
-- url     : https://prove2.me/theorems/42c445f5-17f5-4ae6-89c5-5ee4ce20e225
-- title:
--   Periodic Cubical4: take dual Sweep Order of le
-- statement:
--   The Periodic Cubical4 construction uses the take dual Sweep Order of le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FourDimensionalToricCode/MembraneSweep.lean#L828-L833
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FourDimensionalToricCode/MembraneSweep.lean#L828-L833

import Definitions.Def_QEC_Coding_FourDimensionalToricCode_MembraneSyndrome
import Definitions.Def_QEC_Coding_Stabilizer_TwoDimensional_StripLogicalPath
import Definitions.Def_QEC_Coding_FourDimensionalToricCode_MembraneSweep
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.PeriodicCubical4
open scoped Classical BigOperators
open PauliSymplectic StabilizerCode.LocalStabilizerHamiltonian
variable {L : Nat} [NeZero L] [Fact (1 < L)]

theorem QEC.Coding.PeriodicCubical4.take_dualSweepOrder_of_le (x y : ZMod L) {n : Nat}
    (hn : n ≤ L * L) :
    (dualSweepOrder x y).take n =
      (dualSweepPlaquettes x y).take n := by sorry
