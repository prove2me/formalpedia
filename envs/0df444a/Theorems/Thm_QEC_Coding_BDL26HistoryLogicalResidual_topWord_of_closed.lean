-- Prove2me | Theorems.Thm_QEC_Coding_BDL26HistoryLogicalResidual_topWord_of_closed
-- name    : QEC.Coding.BDL26HistoryLogicalResidual.topWord_of_closed
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T13:43:35.977941+00:00
-- url     : https://prove2.me/theorems/482d45c7-5700-4164-8e78-0febb982f124
-- title:
--   BDL26 History Logical Residual: top Word of closed
-- statement:
--   A closed error survives as itself: this is not a blanket stability claim.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/HistoryLogicalResidual/Words.lean#L147-L160
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/HistoryLogicalResidual/Words.lean#L147-L160

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

theorem QEC.Coding.BDL26HistoryLogicalResidual.topWord_of_closed (sigma : TopInput S n)
    (e : (SuffixData S n).family.Cochain1 (TopIndex n))
    (he : (SuffixData S n).family.coboundary1 (TopIndex n) e = 0) : topWord S n sigma e = e := by sorry
