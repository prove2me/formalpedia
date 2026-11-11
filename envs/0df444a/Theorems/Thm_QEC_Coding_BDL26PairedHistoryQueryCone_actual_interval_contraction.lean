-- Prove2me | Theorems.Thm_QEC_Coding_BDL26PairedHistoryQueryCone_actual_interval_contraction
-- name    : QEC.Coding.BDL26PairedHistoryQueryCone.actual_interval_contraction
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T11:06:22.495516+00:00
-- url     : https://prove2.me/theorems/c2579ad3-bf30-4b89-b6c5-458c25f08f57
-- title:
--   BDL26 Paired History Query Cone: actual interval contraction
-- statement:
--   The BDL26 Paired History Query Cone construction uses the actual interval contraction property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/PairedHistoryQueryCone.lean#L480-L485
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/PairedHistoryQueryCone.lean#L480-L485

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_PairedHistoryQueryCone_ReadBounds
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_HistorySyndromeSensitivity
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_HistoryErrorTelescoping_HistorySums
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_PairedHistoryQueryCone
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26PairedHistoryQueryCone
open BDL26FiniteTannerSquare BDL26DecodingGraph BDL26IndexedDecoder
open BDL26OwnerIncidenceMasks BDL26HistorySyndromeSensitivity
open BDL26HistoryErrorTelescoping MultiscaleDecoder
open scoped Classical BigOperators
variable (S : OddScale) (n : Nat)

theorem QEC.Coding.BDL26PairedHistoryQueryCone.actual_interval_contraction (s : TopInput S n) (a b : LevelIndex n)
    (ha : a.val ≤ b.val) :
    2 ^ rxCount a.val b.val * HammingWeight (actualInputs S n s a).val ≤
      HammingWeight (actualInputs S n s b).val := by sorry
