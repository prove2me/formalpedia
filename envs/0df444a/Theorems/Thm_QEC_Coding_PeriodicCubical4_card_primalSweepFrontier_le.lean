-- Prove2me | Theorems.Thm_QEC_Coding_PeriodicCubical4_card_primalSweepFrontier_le
-- name    : QEC.Coding.PeriodicCubical4.card_primalSweepFrontier_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T03:48:00.108318+00:00
-- url     : https://prove2.me/theorems/35a90766-ed37-4f99-b249-4a779ebd373e
-- title:
--   Periodic Cubical4: card primal Sweep Frontier le
-- statement:
--   The Periodic Cubical4 construction uses the card primal Sweep Frontier le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FourDimensionalToricCode/MembraneSweep.lean#L244-L246
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FourDimensionalToricCode/MembraneSweep.lean#L244-L246

import Definitions.Def_QEC_Coding_FourDimensionalToricCode_MembraneSyndrome
import Definitions.Def_QEC_Coding_Stabilizer_TwoDimensional_StripLogicalPath
import Definitions.Def_QEC_Coding_FourDimensionalToricCode_MembraneSweep
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.PeriodicCubical4
open scoped Classical BigOperators
open PauliSymplectic StabilizerCode.LocalStabilizerHamiltonian
variable {L : Nat} [NeZero L] [Fact (1 < L)]

theorem QEC.Coding.PeriodicCubical4.card_primalSweepFrontier_le (z w : ZMod L) (n : Nat) :
    (primalSweepFrontier z w n).card ≤ 4 * L := by sorry
