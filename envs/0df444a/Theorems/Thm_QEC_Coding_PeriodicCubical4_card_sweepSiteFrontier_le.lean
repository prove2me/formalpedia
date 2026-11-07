-- Prove2me | Theorems.Thm_QEC_Coding_PeriodicCubical4_card_sweepSiteFrontier_le
-- name    : QEC.Coding.PeriodicCubical4.card_sweepSiteFrontier_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T03:32:48.879566+00:00
-- url     : https://prove2.me/theorems/d3092214-1a99-49b7-af5d-857d39c17ed1
-- title:
--   Periodic Cubical4: card sweep Site Frontier le
-- statement:
--   The Periodic Cubical4 construction uses the card sweep Site Frontier le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FourDimensionalToricCode/MembraneSweep.lean#L223-L234
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FourDimensionalToricCode/MembraneSweep.lean#L223-L234

import Definitions.Def_QEC_Coding_FourDimensionalToricCode_MembraneSyndrome
import Definitions.Def_QEC_Coding_Stabilizer_TwoDimensional_StripLogicalPath
import Definitions.Def_QEC_Coding_FourDimensionalToricCode_MembraneSweep
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.PeriodicCubical4
open scoped Classical BigOperators
open PauliSymplectic StabilizerCode.LocalStabilizerHamiltonian
variable {L : Nat} [NeZero L] [Fact (1 < L)]

theorem QEC.Coding.PeriodicCubical4.card_sweepSiteFrontier_le (L n : Nat) :
    (sweepSiteFrontier L n).card ≤ 4 * L := by sorry
