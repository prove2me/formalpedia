-- Prove2me | Theorems.Thm_QEC_Coding_PeriodicCubical4_dualMembraneSweepPath_stateAt_vector_of_membrane_complete
-- name    : QEC.Coding.PeriodicCubical4.dualMembraneSweepPath_stateAt_vector_of_membrane_complete
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T03:50:36.133431+00:00
-- url     : https://prove2.me/theorems/2c8b99d8-d972-4b56-ae7a-39f254dcbbc1
-- title:
--   Periodic Cubical4: dual Membrane Sweep Path state At vector of membrane complete
-- statement:
--   The Periodic Cubical4 construction uses the dual Membrane Sweep Path state At vector of membrane complete property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FourDimensionalToricCode/MembraneSweep.lean#L981-L1015
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FourDimensionalToricCode/MembraneSweep.lean#L981-L1015

import Definitions.Def_QEC_Coding_FourDimensionalToricCode_MembraneSyndrome
import Definitions.Def_QEC_Coding_Stabilizer_TwoDimensional_StripLogicalPath
import Definitions.Def_QEC_Coding_FourDimensionalToricCode_MembraneSweep
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.PeriodicCubical4
open scoped Classical BigOperators
open PauliSymplectic StabilizerCode.LocalStabilizerHamiltonian
variable {L : Nat} [NeZero L] [Fact (1 < L)]

theorem QEC.Coding.PeriodicCubical4.dualMembraneSweepPath_stateAt_vector_of_membrane_complete
    (x y : ZMod L) (n : Nat) (hmembrane : L * L ≤ n)
    (hcore : n ≤ (dualSweepOrder x y).length) :
    ((dualMembraneSweepPath x y).stateAt n).vector =
      (dualMembraneError (dualXYMembrane x y)).vector := by sorry
