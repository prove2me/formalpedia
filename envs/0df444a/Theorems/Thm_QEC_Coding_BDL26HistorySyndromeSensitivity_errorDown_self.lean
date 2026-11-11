-- Prove2me | Theorems.Thm_QEC_Coding_BDL26HistorySyndromeSensitivity_errorDown_self
-- name    : QEC.Coding.BDL26HistorySyndromeSensitivity.errorDown_self
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T10:56:39.504926+00:00
-- url     : https://prove2.me/theorems/cca4c1a4-df9c-46d7-b1e9-db668776b1ae
-- title:
--   BDL26 History Syndrome Sensitivity: error Down self
-- statement:
--   The BDL26 History Syndrome Sensitivity construction uses the error Down self property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/HistorySyndromeSensitivity/Preimages.lean#L91-L98
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/HistorySyndromeSensitivity/Preimages.lean#L91-L98

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_HistorySyndromeSensitivity_Snapshots
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXErrorPullback
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RZErrorPullback
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_HistorySyndromeSensitivity_Preimages
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26HistorySyndromeSensitivity
open BDL26FiniteTannerSquare BDL26IndexedDecoder BDL26OwnerIncidenceMasks
open MultiscaleDecoder
open scoped Classical
variable (S : OddScale) (n : Nat)

theorem QEC.Coding.BDL26HistorySyndromeSensitivity.errorDown_self (b : Nat) (hb : b ≤ n)
    (e : (SuffixData S n).family.Cochain1 ⟨b,Nat.lt_succ_of_le hb⟩) :
    errorDown S n b hb e ⟨b,Nat.lt_succ_of_le hb⟩ (Nat.le_refl _) = e := by sorry
