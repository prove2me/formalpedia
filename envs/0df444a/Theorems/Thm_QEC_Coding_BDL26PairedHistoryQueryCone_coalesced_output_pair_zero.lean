-- Prove2me | Theorems.Thm_QEC_Coding_BDL26PairedHistoryQueryCone_coalesced_output_pair_zero
-- name    : QEC.Coding.BDL26PairedHistoryQueryCone.coalesced_output_pair_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T11:20:27.439189+00:00
-- url     : https://prove2.me/theorems/a2e17746-e1e5-47d6-94a4-967b5f2fbe90
-- title:
--   BDL26 Paired History Query Cone: coalesced output pair zero
-- statement:
--   The BDL26 Paired History Query Cone construction uses the coalesced output pair zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/PairedHistoryQueryCone.lean#L552-L559
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/PairedHistoryQueryCone.lean#L552-L559

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

theorem QEC.Coding.BDL26PairedHistoryQueryCone.coalesced_output_pair_zero (s : TopInput S n) (e : TopWord S n)
    (a : LevelIndex n)
    (hs : actualInputs S n s a = actualInputs S n (perturbTop S n s e) a)
    (i : StepIndex n) (hi : i.val < a.val) :
    (actualOutput S n s i).correction +
      (actualOutput S n (perturbTop S n s e) i).correction = 0 := by sorry
