-- Prove2me | Theorems.Thm_QEC_Coding_BDL26HistoryLogicalResidual_coefficient_equality
-- name    : QEC.Coding.BDL26HistoryLogicalResidual.coefficient_equality
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T13:44:26.718311+00:00
-- url     : https://prove2.me/theorems/cf56d31c-5f4c-4300-acf4-31a4edffe33f
-- title:
--   BDL26 History Logical Residual: coefficient equality
-- statement:
--   The BDL26 History Logical Residual construction uses the coefficient equality property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/HistoryLogicalResidual.lean#L52-L58
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/HistoryLogicalResidual.lean#L52-L58

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

theorem QEC.Coding.BDL26HistoryLogicalResidual.coefficient_equality (sigma : TopInput S n)
    (e u : (SuffixData S n).family.Cochain1 (TopIndex n))
    (hu : (SuffixData S n).family.coboundary1 (TopIndex n) u = sigma.val) :
    topCoefficient S n sigma e = lowerCoefficient S n sigma e u hu := by sorry
