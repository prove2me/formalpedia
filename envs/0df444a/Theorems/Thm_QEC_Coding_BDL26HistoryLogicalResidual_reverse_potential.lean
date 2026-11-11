-- Prove2me | Theorems.Thm_QEC_Coding_BDL26HistoryLogicalResidual_reverse_potential
-- name    : QEC.Coding.BDL26HistoryLogicalResidual.reverse_potential
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-10T19:08:41.209216+00:00
-- url     : https://prove2.me/theorems/b5204bed-45c9-493c-a70d-60bcd5583447
-- title:
--   BDL26 History Logical Residual: reverse potential
-- statement:
--   The BDL26 History Logical Residual construction uses the reverse potential property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/HistoryLogicalResidual.lean#L114-L121
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/HistoryLogicalResidual.lean#L114-L121

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

theorem QEC.Coding.BDL26HistoryLogicalResidual.reverse_potential (sigma : TopInput S n)
    (e u : (SuffixData S n).family.Cochain1 (TopIndex n))
    (hu : (SuffixData S n).family.coboundary1 (TopIndex n) u = sigma.val)
    (ftop : (SuffixData S n).family.Cochain0 (TopIndex n))
    (hftop : (SuffixData S n).family.coboundary0 (TopIndex n) ftop = topWord S n sigma e) :
    ∃ f2 : (SuffixData S n).family.Cochain0 0,
      (SuffixData S n).family.coboundary0 0 f2 = lowerWord S n sigma e u := by sorry
