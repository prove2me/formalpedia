-- Prove2me | Theorems.Thm_QEC_Coding_PeriodicCubical4_primalSweepRegion_subset
-- name    : QEC.Coding.PeriodicCubical4.primalSweepRegion_subset
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T03:30:22.254061+00:00
-- url     : https://prove2.me/theorems/478da7f4-fc06-45c6-be7b-8ed0be980276
-- title:
--   Periodic Cubical4: primal Sweep Region subset
-- statement:
--   The Periodic Cubical4 construction uses the primal Sweep Region subset property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FourDimensionalToricCode/MembraneSweep.lean#L173-L178
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FourDimensionalToricCode/MembraneSweep.lean#L173-L178

import Definitions.Def_QEC_Coding_FourDimensionalToricCode_MembraneSyndrome
import Definitions.Def_QEC_Coding_Stabilizer_TwoDimensional_StripLogicalPath
import Definitions.Def_QEC_Coding_FourDimensionalToricCode_MembraneSweep
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.PeriodicCubical4
open scoped Classical BigOperators
open PauliSymplectic StabilizerCode.LocalStabilizerHamiltonian
variable {L : Nat} [NeZero L] [Fact (1 < L)]

theorem QEC.Coding.PeriodicCubical4.primalSweepRegion_subset (z w : ZMod L) (n : Nat) :
    primalSweepRegion z w n ⊆ (primalSweepPlaquettes z w).toFinset := by sorry
