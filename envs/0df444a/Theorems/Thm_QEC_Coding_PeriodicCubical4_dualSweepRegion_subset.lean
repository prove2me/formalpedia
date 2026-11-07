-- Prove2me | Theorems.Thm_QEC_Coding_PeriodicCubical4_dualSweepRegion_subset
-- name    : QEC.Coding.PeriodicCubical4.dualSweepRegion_subset
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T03:32:23.676207+00:00
-- url     : https://prove2.me/theorems/13d3e196-256e-44a1-b9c8-04f4e283741e
-- title:
--   Periodic Cubical4: dual Sweep Region subset
-- statement:
--   The Periodic Cubical4 construction uses the dual Sweep Region subset property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FourDimensionalToricCode/MembraneSweep.lean#L180-L185
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FourDimensionalToricCode/MembraneSweep.lean#L180-L185

import Definitions.Def_QEC_Coding_FourDimensionalToricCode_MembraneSyndrome
import Definitions.Def_QEC_Coding_Stabilizer_TwoDimensional_StripLogicalPath
import Definitions.Def_QEC_Coding_FourDimensionalToricCode_MembraneSweep
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.PeriodicCubical4
open scoped Classical BigOperators
open PauliSymplectic StabilizerCode.LocalStabilizerHamiltonian
variable {L : Nat} [NeZero L] [Fact (1 < L)]

theorem QEC.Coding.PeriodicCubical4.dualSweepRegion_subset (x y : ZMod L) (n : Nat) :
    dualSweepRegion x y n ⊆ (dualSweepPlaquettes x y).toFinset := by sorry
