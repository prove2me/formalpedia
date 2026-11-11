-- Prove2me | Theorems.Thm_QEC_Coding_BDL26HistoryLogicalResidual_lower_zero_iff_boundary
-- name    : QEC.Coding.BDL26HistoryLogicalResidual.lower_zero_iff_boundary
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T13:43:45.479172+00:00
-- url     : https://prove2.me/theorems/fb8844a1-1650-4c30-a7f8-5419bab621eb
-- title:
--   BDL26 History Logical Residual: lower zero iff boundary
-- statement:
--   The BDL26 History Logical Residual construction uses the lower zero iff boundary property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/HistoryLogicalResidual.lean#L81-L91
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/HistoryLogicalResidual.lean#L81-L91

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

theorem QEC.Coding.BDL26HistoryLogicalResidual.lower_zero_iff_boundary (sigma : TopInput S n)
    (e u : (SuffixData S n).family.Cochain1 (TopIndex n))
    (hu : (SuffixData S n).family.coboundary1 (TopIndex n) u = sigma.val) :
    lowerCoefficient S n sigma e u hu = 0 ↔
      ∃ f : (SuffixData S n).family.Cochain0 0,
        (SuffixData S n).family.coboundary0 0 f = lowerWord S n sigma e u := by sorry
