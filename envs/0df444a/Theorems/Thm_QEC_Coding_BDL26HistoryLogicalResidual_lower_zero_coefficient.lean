-- Prove2me | Theorems.Thm_QEC_Coding_BDL26HistoryLogicalResidual_lower_zero_coefficient
-- name    : QEC.Coding.BDL26HistoryLogicalResidual.lower_zero_coefficient
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-10T19:49:34.760526+00:00
-- url     : https://prove2.me/theorems/e5bdddef-da6d-4e09-bbf9-c88d67aca2b8
-- title:
--   BDL26 History Logical Residual: lower zero coefficient
-- statement:
--   The BDL26 History Logical Residual construction uses the lower zero coefficient property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/HistoryLogicalResidual.lean#L188-L192
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/HistoryLogicalResidual.lean#L188-L192

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

theorem QEC.Coding.BDL26HistoryLogicalResidual.lower_zero_coefficient (sigma : TopInput S n)
    (u : (SuffixData S n).family.Cochain1 (TopIndex n))
    (hu : (SuffixData S n).family.coboundary1 (TopIndex n) u = sigma.val) :
    lowerCoefficient S n sigma 0 u hu = 0 := by sorry
