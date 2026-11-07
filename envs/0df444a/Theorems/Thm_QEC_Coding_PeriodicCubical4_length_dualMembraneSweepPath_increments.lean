-- Prove2me | Theorems.Thm_QEC_Coding_PeriodicCubical4_length_dualMembraneSweepPath_increments
-- name    : QEC.Coding.PeriodicCubical4.length_dualMembraneSweepPath_increments
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T03:28:51.724451+00:00
-- url     : https://prove2.me/theorems/8ae74365-6adc-44cd-88ae-e04996660a91
-- title:
--   Periodic Cubical4: length dual Membrane Sweep Path increments
-- statement:
--   The Periodic Cubical4 construction uses the length dual Membrane Sweep Path increments property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FourDimensionalToricCode/MembraneSweep.lean#L939-L943
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FourDimensionalToricCode/MembraneSweep.lean#L939-L943

import Definitions.Def_QEC_Coding_FourDimensionalToricCode_MembraneSyndrome
import Definitions.Def_QEC_Coding_Stabilizer_TwoDimensional_StripLogicalPath
import Definitions.Def_QEC_Coding_FourDimensionalToricCode_MembraneSweep
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.PeriodicCubical4
open scoped Classical BigOperators
open PauliSymplectic StabilizerCode.LocalStabilizerHamiltonian
variable {L : Nat} [NeZero L] [Fact (1 < L)]

theorem QEC.Coding.PeriodicCubical4.length_dualMembraneSweepPath_increments (x y : ZMod L) :
    (dualMembraneSweepPath x y).increments.length =
      (dualSweepOrder x y).length + 1 := by sorry
