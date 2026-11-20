-- Prove2me | Theorems.Thm_QEC_Coding_BDL26LocalBackgroundComparisonDepth_budgetDepth_rx_count
-- name    : QEC.Coding.BDL26LocalBackgroundComparisonDepth.budgetDepth_rx_count
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T14:28:34.52161+00:00
-- url     : https://prove2.me/theorems/31e66bf6-0595-4666-86c6-31d625a87e64
-- title:
--   BDL26 Local Background Comparison Depth: budget Depth rx count
-- statement:
--   The BDL26 Local Background Comparison Depth construction uses the budget Depth rx count property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/LocalBackgroundComparisonDepth.lean#L89-L91
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/LocalBackgroundComparisonDepth.lean#L89-L91

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_LocalBackgroundComparisonResponse
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_UniformReadoutWeight
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_LocalBackgroundComparisonDepth
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26LocalBackgroundComparisonDepth
open MultiscaleDecoder BDL26FiniteTannerSquare BDL26DecodingGraph
open BDL26IndexedDecoder BDL26OwnerIncidenceMasks BDL26HistorySyndromeSensitivity
open BDL26HistoryErrorTelescoping BDL26HistoryLogicalResidual BDL26RZMap1CoordinateBridge
open BDL26LocalBackgroundComparisonResponse
open scoped Classical BigOperators

theorem QEC.Coding.BDL26LocalBackgroundComparisonDepth.budgetDepth_rx_count (B : Nat) : (budgetDepth B+1)/2=4*B+1 := by sorry
