-- Prove2me | Theorems.Thm_QEC_Coding_BDL26PairedHistoryQueryCone_stoppingLevel_coalesces
-- name    : QEC.Coding.BDL26PairedHistoryQueryCone.stoppingLevel_coalesces
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T11:18:38.77661+00:00
-- url     : https://prove2.me/theorems/a3a0858d-9d2e-4222-a2bd-b0a3b83a5d2a
-- title:
--   BDL26 Paired History Query Cone: stopping Level coalesces
-- statement:
--   The BDL26 Paired History Query Cone construction uses the stopping Level coalesces property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/PairedHistoryQueryCone.lean#L282-L293
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/PairedHistoryQueryCone.lean#L282-L293

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

theorem QEC.Coding.BDL26PairedHistoryQueryCone.stoppingLevel_coalesces (s : TopInput S n) (e : TopWord S n)
    (ha : 0 < (stoppingLevel S n s e).val) :
    actualInputs S n s (stoppingLevel S n s e) =
      actualInputs S n (perturbTop S n s e) (stoppingLevel S n s e) := by sorry
