-- Prove2me | Theorems.Thm_QEC_Coding_BDL26HistoryErrorTelescoping_actualInputs_prefix
-- name    : QEC.Coding.BDL26HistoryErrorTelescoping.actualInputs_prefix
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T11:21:10.301203+00:00
-- url     : https://prove2.me/theorems/f51c9cc3-4444-49dd-8594-2967ed8da8b4
-- title:
--   BDL26 History Error Telescoping: actual Inputs prefix
-- statement:
--   The BDL26 History Error Telescoping construction uses the actual Inputs prefix property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/HistoryErrorTelescoping.lean#L63-L70
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/HistoryErrorTelescoping.lean#L63-L70

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_HistoryErrorTelescoping_HistorySums
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_HistorySyndromeSensitivity
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_HistoryErrorTelescoping
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26HistoryErrorTelescoping
open MultiscaleDecoder BDL26HistorySyndromeSensitivity
open BDL26FiniteTannerSquare BDL26IndexedDecoder BDL26OwnerIncidenceMasks
open scoped Classical
universe u v w
variable (S : OddScale) (n : Nat)

theorem QEC.Coding.BDL26HistoryErrorTelescoping.actualInputs_prefix (sigma : TopInput S n) (a b : LevelIndex n)
    (hab : a.val ≤ b.val) :
    prefixInput (SuffixData S n)
      (LevelTwoHistory.suffixSteps _ (actualAboveTwoSteps S n)) b.val
      (Nat.le_of_lt_succ b.isLt) (actualInputs S n sigma b) a hab = actualInputs S n sigma a := by sorry
