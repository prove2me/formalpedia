-- Prove2me | Theorems.Thm_QEC_Coding_BDL26HistoryLogicalResidual_class_relation
-- name    : QEC.Coding.BDL26HistoryLogicalResidual.class_relation
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T13:45:44.872616+00:00
-- url     : https://prove2.me/theorems/92c115c4-8f7d-4de7-8574-7dd605526970
-- title:
--   BDL26 History Logical Residual: class relation
-- statement:
--   The quotient relation is induced by the literal intervalMap1 on full words.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/HistoryLogicalResidual.lean#L29-L50
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/HistoryLogicalResidual.lean#L29-L50

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

theorem QEC.Coding.BDL26HistoryLogicalResidual.class_relation (sigma : TopInput S n)
    (e u : (SuffixData S n).family.Cochain1 (TopIndex n))
    (hu : (SuffixData S n).family.coboundary1 (TopIndex n) u = sigma.val) :
    FC.classOf S (n+2) (topCocycle S n sigma e) =
      suffixEquiv S n 0 (TopIndex n) (FC.classOf S 2 (lowerCocycle S n sigma e u hu)) := by sorry
