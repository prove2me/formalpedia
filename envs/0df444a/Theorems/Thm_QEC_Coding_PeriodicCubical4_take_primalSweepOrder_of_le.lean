-- Prove2me | Theorems.Thm_QEC_Coding_PeriodicCubical4_take_primalSweepOrder_of_le
-- name    : QEC.Coding.PeriodicCubical4.take_primalSweepOrder_of_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T03:49:16.34551+00:00
-- url     : https://prove2.me/theorems/52a31ba0-e4e8-47d6-bc72-c7e87a127673
-- title:
--   Periodic Cubical4: take primal Sweep Order of le
-- statement:
--   The Periodic Cubical4 construction uses the take primal Sweep Order of le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FourDimensionalToricCode/MembraneSweep.lean#L821-L826
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FourDimensionalToricCode/MembraneSweep.lean#L821-L826

import Definitions.Def_QEC_Coding_FourDimensionalToricCode_MembraneSyndrome
import Definitions.Def_QEC_Coding_Stabilizer_TwoDimensional_StripLogicalPath
import Definitions.Def_QEC_Coding_FourDimensionalToricCode_MembraneSweep
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.PeriodicCubical4
open scoped Classical BigOperators
open PauliSymplectic StabilizerCode.LocalStabilizerHamiltonian
variable {L : Nat} [NeZero L] [Fact (1 < L)]

theorem QEC.Coding.PeriodicCubical4.take_primalSweepOrder_of_le (z w : ZMod L) {n : Nat}
    (hn : n ≤ L * L) :
    (primalSweepOrder z w).take n =
      (primalSweepPlaquettes z w).take n := by sorry
