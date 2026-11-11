-- Prove2me | Theorems.Thm_QEC_Coding_BDL26PairedHistoryQueryCone_output_eq_below
-- name    : QEC.Coding.BDL26PairedHistoryQueryCone.output_eq_below
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T11:20:08.968041+00:00
-- url     : https://prove2.me/theorems/cb92fdc7-12cb-4ea4-a315-3dbc45d3e63e
-- title:
--   BDL26 Paired History Query Cone: output eq below
-- statement:
--   The BDL26 Paired History Query Cone construction uses the output eq below property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/PairedHistoryQueryCone.lean#L493-L498
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/PairedHistoryQueryCone.lean#L493-L498

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

theorem QEC.Coding.BDL26PairedHistoryQueryCone.output_eq_below (s t : TopInput S n) (a : LevelIndex n)
    (hs : actualInputs S n s a = actualInputs S n t a)
    (i : StepIndex n) (hi : i.succ.val ≤ a.val) :
    actualOutput S n s i = actualOutput S n t i := by sorry
