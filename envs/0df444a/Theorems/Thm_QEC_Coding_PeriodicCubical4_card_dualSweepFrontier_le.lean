-- Prove2me | Theorems.Thm_QEC_Coding_PeriodicCubical4_card_dualSweepFrontier_le
-- name    : QEC.Coding.PeriodicCubical4.card_dualSweepFrontier_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T03:47:52.370659+00:00
-- url     : https://prove2.me/theorems/842196ba-1ffe-4d2d-9f33-e23fe6e0f15a
-- title:
--   Periodic Cubical4: card dual Sweep Frontier le
-- statement:
--   The Periodic Cubical4 construction uses the card dual Sweep Frontier le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FourDimensionalToricCode/MembraneSweep.lean#L248-L250
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FourDimensionalToricCode/MembraneSweep.lean#L248-L250

import Definitions.Def_QEC_Coding_FourDimensionalToricCode_MembraneSyndrome
import Definitions.Def_QEC_Coding_Stabilizer_TwoDimensional_StripLogicalPath
import Definitions.Def_QEC_Coding_FourDimensionalToricCode_MembraneSweep
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.PeriodicCubical4
open scoped Classical BigOperators
open PauliSymplectic StabilizerCode.LocalStabilizerHamiltonian
variable {L : Nat} [NeZero L] [Fact (1 < L)]

theorem QEC.Coding.PeriodicCubical4.card_dualSweepFrontier_le (x y : ZMod L) (n : Nat) :
    (dualSweepFrontier x y n).card ≤ 4 * L := by sorry
