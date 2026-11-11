-- Prove2me | Theorems.Thm_QEC_Coding_BDL26HistoryLogicalResidual_top_zero_iff_boundary
-- name    : QEC.Coding.BDL26HistoryLogicalResidual.top_zero_iff_boundary
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T13:45:34.488891+00:00
-- url     : https://prove2.me/theorems/10250c8f-5421-406b-851c-dfc79f7b545a
-- title:
--   BDL26 History Logical Residual: top zero iff boundary
-- statement:
--   The BDL26 History Logical Residual construction uses the top zero iff boundary property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/HistoryLogicalResidual.lean#L72-L79
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/HistoryLogicalResidual.lean#L72-L79

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

theorem QEC.Coding.BDL26HistoryLogicalResidual.top_zero_iff_boundary (sigma : TopInput S n)
    (e : (SuffixData S n).family.Cochain1 (TopIndex n)) :
    topCoefficient S n sigma e = 0 ↔
      ∃ f : (SuffixData S n).family.Cochain0 (TopIndex n),
        (SuffixData S n).family.coboundary0 (TopIndex n) f = topWord S n sigma e := by sorry
