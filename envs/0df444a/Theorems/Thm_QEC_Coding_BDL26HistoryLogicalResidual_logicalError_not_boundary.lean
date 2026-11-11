-- Prove2me | Theorems.Thm_QEC_Coding_BDL26HistoryLogicalResidual_logicalError_not_boundary
-- name    : QEC.Coding.BDL26HistoryLogicalResidual.logicalError_not_boundary
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T13:46:58.258453+00:00
-- url     : https://prove2.me/theorems/f78d954b-047f-4e2c-a7f0-5a7e23b7809c
-- title:
--   BDL26 History Logical Residual: logical Error not boundary
-- statement:
--   The BDL26 History Logical Residual construction uses the logical Error not boundary property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/HistoryLogicalResidual.lean#L166-L172
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/HistoryLogicalResidual.lean#L166-L172

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

theorem QEC.Coding.BDL26HistoryLogicalResidual.logicalError_not_boundary (sigma : TopInput S n) :
    ¬ ∃ f : (SuffixData S n).family.Cochain0 (TopIndex n),
      (SuffixData S n).family.coboundary0 (TopIndex n) f = topWord S n sigma (logicalError S n) := by sorry
