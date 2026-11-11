-- Prove2me | Theorems.Thm_QEC_Coding_BDL26HistoryLogicalResidual_pureX_coefficient_equality
-- name    : QEC.Coding.BDL26HistoryLogicalResidual.pureX_coefficient_equality
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-10T19:06:28.880217+00:00
-- url     : https://prove2.me/theorems/8a05d518-bab8-4310-928c-afa51e4babd5
-- title:
--   BDL26 History Logical Residual: pure X coefficient equality
-- statement:
--   The BDL26 History Logical Residual construction uses the pure X coefficient equality property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/HistoryLogicalResidual.lean#L60-L70
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/HistoryLogicalResidual.lean#L60-L70

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

theorem QEC.Coding.BDL26HistoryLogicalResidual.pureX_coefficient_equality (sigma : TopInput S n)
    (e u : (SuffixData S n).family.Cochain1 (TopIndex n))
    (hu : (SuffixData S n).family.coboundary1 (TopIndex n) u = sigma.val) :
    BDL26LogicalQubitPreservation.logicalEquiv S (n+2)
        (BDL26LogicalQubitPreservation.logicalClass S (n+2)
          (pureX S (n+2) (topCocycle S n sigma e))) =
      BDL26LogicalQubitPreservation.logicalEquiv S 2
        (BDL26LogicalQubitPreservation.logicalClass S 2
          (pureX S 2 (lowerCocycle S n sigma e u hu))) := by sorry
