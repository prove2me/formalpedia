-- Prove2me | Theorems.Thm_QEC_Coding_PeriodicCubical4_primalLoopLength_primalXYMembrane
-- name    : QEC.Coding.PeriodicCubical4.primalLoopLength_primalXYMembrane
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T03:28:53.978203+00:00
-- url     : https://prove2.me/theorems/73f6a95d-459d-4c06-8704-06b86c04a08d
-- title:
--   Periodic Cubical4: primal Loop Length primal XYMembrane
-- statement:
--   The Periodic Cubical4 construction uses the primal Loop Length primal XYMembrane property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FourDimensionalToricCode/MembraneSweep.lean#L1017-L1020
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FourDimensionalToricCode/MembraneSweep.lean#L1017-L1020

import Definitions.Def_QEC_Coding_FourDimensionalToricCode_MembraneSyndrome
import Definitions.Def_QEC_Coding_Stabilizer_TwoDimensional_StripLogicalPath
import Definitions.Def_QEC_Coding_FourDimensionalToricCode_MembraneSweep
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.PeriodicCubical4
open scoped Classical BigOperators
open PauliSymplectic StabilizerCode.LocalStabilizerHamiltonian
variable {L : Nat} [NeZero L] [Fact (1 < L)]

theorem QEC.Coding.PeriodicCubical4.primalLoopLength_primalXYMembrane (z w : ZMod L) :
    primalLoopLength (primalXYMembrane z w) = 0 := by sorry
