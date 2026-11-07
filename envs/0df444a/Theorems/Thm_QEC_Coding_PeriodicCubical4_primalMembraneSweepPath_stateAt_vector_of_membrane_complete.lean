-- Prove2me | Theorems.Thm_QEC_Coding_PeriodicCubical4_primalMembraneSweepPath_stateAt_vector_of_membrane_complete
-- name    : QEC.Coding.PeriodicCubical4.primalMembraneSweepPath_stateAt_vector_of_membrane_complete
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T03:49:22.379829+00:00
-- url     : https://prove2.me/theorems/93b94a1b-ea7f-4777-9eae-4a77c3240bd8
-- title:
--   Periodic Cubical4: primal Membrane Sweep Path state At vector of membrane complete
-- statement:
--   The Periodic Cubical4 construction uses the primal Membrane Sweep Path state At vector of membrane complete property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FourDimensionalToricCode/MembraneSweep.lean#L945-L979
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FourDimensionalToricCode/MembraneSweep.lean#L945-L979

import Definitions.Def_QEC_Coding_FourDimensionalToricCode_MembraneSyndrome
import Definitions.Def_QEC_Coding_Stabilizer_TwoDimensional_StripLogicalPath
import Definitions.Def_QEC_Coding_FourDimensionalToricCode_MembraneSweep
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.PeriodicCubical4
open scoped Classical BigOperators
open PauliSymplectic StabilizerCode.LocalStabilizerHamiltonian
variable {L : Nat} [NeZero L] [Fact (1 < L)]

theorem QEC.Coding.PeriodicCubical4.primalMembraneSweepPath_stateAt_vector_of_membrane_complete
    (z w : ZMod L) (n : Nat) (hmembrane : L * L ≤ n)
    (hcore : n ≤ (primalSweepOrder z w).length) :
    ((primalMembraneSweepPath z w).stateAt n).vector =
      (primalMembraneError (primalXYMembrane z w)).vector := by sorry
