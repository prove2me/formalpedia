-- Prove2me | Theorems.Thm_QEC_Coding_BDL26HistoryLogicalResidual_cocycleEdge_word
-- name    : QEC.Coding.BDL26HistoryLogicalResidual.cocycleEdge_word
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T11:24:24.658267+00:00
-- url     : https://prove2.me/theorems/4d404291-c055-4167-95e7-730d326ed02a
-- title:
--   BDL26 History Logical Residual: cocycle Edge word
-- statement:
--   The BDL26 History Logical Residual construction uses the cocycle Edge word property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/HistoryLogicalResidual/Intervals.lean#L40-L43
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/HistoryLogicalResidual/Intervals.lean#L40-L43

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_HistoryErrorTelescoping
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_LogicalQubitPreservation
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_HistoryLogicalResidual_Intervals
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26HistoryLogicalResidual
open MultiscaleDecoder BDL26HistorySyndromeSensitivity BDL26HistoryErrorTelescoping
open BDL26FiniteTannerSquare BDL26DecodingGraph BDL26IndexedDecoder
open BDL26RZMap1CoordinateBridge
open scoped Classical
variable (S : OddScale) (n : Nat)

theorem QEC.Coding.BDL26HistoryLogicalResidual.cocycleEdge_word (i : StepIndex n) (w : FC.Cocycle S (i.castSucc.val+2)) :
    (cocycleEdge S n i w).val = ((SuffixData S n).selectedMap i).map1 w.val := by sorry
