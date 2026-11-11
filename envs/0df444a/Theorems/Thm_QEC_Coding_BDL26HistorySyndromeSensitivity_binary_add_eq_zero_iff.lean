-- Prove2me | Theorems.Thm_QEC_Coding_BDL26HistorySyndromeSensitivity_binary_add_eq_zero_iff
-- name    : QEC.Coding.BDL26HistorySyndromeSensitivity.binary_add_eq_zero_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T06:29:09.480085+00:00
-- url     : https://prove2.me/theorems/74f17ccf-be41-40b5-a90f-d05aeac618c2
-- title:
--   BDL26 History Syndrome Sensitivity: binary add eq zero iff
-- statement:
--   The BDL26 History Syndrome Sensitivity construction uses the binary add eq zero iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/HistorySyndromeSensitivity/Steps.lean#L19-L26
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/HistorySyndromeSensitivity/Steps.lean#L19-L26

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXInfluenceBounds
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_History
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_HistorySyndromeSensitivity_Steps
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26HistorySyndromeSensitivity
open BDL26FiniteTannerSquare BDL26DecodingGraph BDL26IndexedDecoder
open BDL26OwnerIncidenceMasks BDL26RXDecoderAdapter BDL26RZDecoderAdapter
open BDL26RXCoarseInfluence BDL26RXInfluenceBounds MultiscaleDecoder
open RXCoarseGraining RXCoarseGraining.RXCoarseGrainingData
open scoped Classical BigOperators

theorem QEC.Coding.BDL26HistorySyndromeSensitivity.binary_add_eq_zero_iff (a b : BDL26Field) : a + b = 0 ↔ a = b := by sorry
