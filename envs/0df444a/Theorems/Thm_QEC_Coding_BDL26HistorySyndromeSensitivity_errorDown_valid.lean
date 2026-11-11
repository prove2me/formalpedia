-- Prove2me | Theorems.Thm_QEC_Coding_BDL26HistorySyndromeSensitivity_errorDown_valid
-- name    : QEC.Coding.BDL26HistorySyndromeSensitivity.errorDown_valid
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T10:56:36.093392+00:00
-- url     : https://prove2.me/theorems/85f91921-7c0e-4fb1-9b0f-402a5a7859ee
-- title:
--   BDL26 History Syndrome Sensitivity: error Down valid
-- statement:
--   The BDL26 History Syndrome Sensitivity construction uses the error Down valid property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/HistorySyndromeSensitivity/Preimages.lean#L111-L136
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/HistorySyndromeSensitivity/Preimages.lean#L111-L136

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

theorem QEC.Coding.BDL26HistorySyndromeSensitivity.errorDown_valid (b : Nat) (hb : b ≤ n)
    (e : (SuffixData S n).family.Cochain1 ⟨b,Nat.lt_succ_of_le hb⟩)
    (sigma : (SuffixData S n).family.Syndrome ⟨b,Nat.lt_succ_of_le hb⟩)
    (he : (SuffixData S n).family.coboundary1 _ e = sigma.val)
    (a : LevelIndex n) (ha : a.val ≤ b) :
    (SuffixData S n).family.coboundary1 a (errorDown S n b hb e a ha) =
      (prefixInput (SuffixData S n)
        (LevelTwoHistory.suffixSteps _ (actualAboveTwoSteps S n)) b hb sigma a ha).val := by sorry
