-- Prove2me | Theorems.Thm_QEC_Coding_BDL26PairedHistoryQueryCone_potential_support
-- name    : QEC.Coding.BDL26PairedHistoryQueryCone.potential_support
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T11:02:09.737815+00:00
-- url     : https://prove2.me/theorems/4d565c75-0622-4f6f-b339-7d5cc9df3213
-- title:
--   BDL26 Paired History Query Cone: potential support
-- statement:
--   The BDL26 Paired History Query Cone construction uses the potential support property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/PairedHistoryQueryCone.lean#L31-L44
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/PairedHistoryQueryCone.lean#L31-L44

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

theorem QEC.Coding.BDL26PairedHistoryQueryCone.potential_support (s : TopInput S n) (e : TopWord S n) (a : LevelIndex n) :
    hammingSupport ((actualInputs S n s a).val +
      (actualInputs S n (perturbTop S n s e) a).val) ⊆ potential S n e a := by sorry
