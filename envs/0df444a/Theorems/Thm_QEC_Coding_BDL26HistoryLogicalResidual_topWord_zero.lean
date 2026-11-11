-- Prove2me | Theorems.Thm_QEC_Coding_BDL26HistoryLogicalResidual_topWord_zero
-- name    : QEC.Coding.BDL26HistoryLogicalResidual.topWord_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T13:47:42.64885+00:00
-- url     : https://prove2.me/theorems/02611e43-15b0-44da-b742-45531afac3b3
-- title:
--   BDL26 History Logical Residual: top Word zero
-- statement:
--   The BDL26 History Logical Residual construction uses the top Word zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/HistoryLogicalResidual/Words.lean#L162-L163
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/HistoryLogicalResidual/Words.lean#L162-L163

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_HistoryLogicalResidual_Intervals
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_HistoryLogicalResidual_Words
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26HistoryLogicalResidual
open MultiscaleDecoder BDL26HistorySyndromeSensitivity BDL26HistoryErrorTelescoping
open BDL26FiniteTannerSquare BDL26DecodingGraph BDL26IndexedDecoder BDL26OwnerIncidenceMasks
open BDL26RZMap1CoordinateBridge
open scoped Classical
variable (S : OddScale) (n : Nat)

theorem QEC.Coding.BDL26HistoryLogicalResidual.topWord_zero (sigma : TopInput S n) : topWord S n sigma 0 = 0 := by sorry
