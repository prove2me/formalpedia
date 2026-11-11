-- Prove2me | Theorems.Thm_QEC_Coding_BDL26HistoryLogicalResidual_logicalError_closed
-- name    : QEC.Coding.BDL26HistoryLogicalResidual.logicalError_closed
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T13:45:25.254804+00:00
-- url     : https://prove2.me/theorems/bcb485d5-9d11-4874-8f13-efb2436547ac
-- title:
--   BDL26 History Logical Residual: logical Error closed
-- statement:
--   The BDL26 History Logical Residual construction uses the logical Error closed property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/HistoryLogicalResidual.lean#L148-L151
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/HistoryLogicalResidual.lean#L148-L151

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_HistoryLogicalResidual_Words
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_HistoryLogicalResidual
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26HistoryLogicalResidual
open MultiscaleDecoder BDL26HistorySyndromeSensitivity BDL26HistoryErrorTelescoping
open BDL26FiniteTannerSquare BDL26DecodingGraph BDL26IndexedDecoder
open BDL26RZMap1CoordinateBridge
open scoped Classical
variable (S : OddScale) (n : Nat)

theorem QEC.Coding.BDL26HistoryLogicalResidual.logicalError_closed :
    (SuffixData S n).family.coboundary1 (TopIndex n) (logicalError S n) = 0 := by sorry
