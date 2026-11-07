-- Prove2me | Theorems.Thm_QEC_Coding_PeriodicCubical4_length_primalMembraneSweepPath_increments
-- name    : QEC.Coding.PeriodicCubical4.length_primalMembraneSweepPath_increments
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T03:29:08.681231+00:00
-- url     : https://prove2.me/theorems/475698e4-bf42-408b-b4e8-19d7a704f866
-- title:
--   Periodic Cubical4: length primal Membrane Sweep Path increments
-- statement:
--   The Periodic Cubical4 construction uses the length primal Membrane Sweep Path increments property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FourDimensionalToricCode/MembraneSweep.lean#L933-L937
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FourDimensionalToricCode/MembraneSweep.lean#L933-L937

import Definitions.Def_QEC_Coding_FourDimensionalToricCode_MembraneSyndrome
import Definitions.Def_QEC_Coding_Stabilizer_TwoDimensional_StripLogicalPath
import Definitions.Def_QEC_Coding_FourDimensionalToricCode_MembraneSweep
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.PeriodicCubical4
open scoped Classical BigOperators
open PauliSymplectic StabilizerCode.LocalStabilizerHamiltonian
variable {L : Nat} [NeZero L] [Fact (1 < L)]

theorem QEC.Coding.PeriodicCubical4.length_primalMembraneSweepPath_increments (z w : ZMod L) :
    (primalMembraneSweepPath z w).increments.length =
      (primalSweepOrder z w).length + 1 := by sorry
