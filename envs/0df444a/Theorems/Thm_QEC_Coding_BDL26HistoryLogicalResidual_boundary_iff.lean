-- Prove2me | Theorems.Thm_QEC_Coding_BDL26HistoryLogicalResidual_boundary_iff
-- name    : QEC.Coding.BDL26HistoryLogicalResidual.boundary_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T13:46:02.239639+00:00
-- url     : https://prove2.me/theorems/7a0000bf-83e6-42b1-8935-358068a5204f
-- title:
--   BDL26 History Logical Residual: boundary iff
-- statement:
--   The BDL26 History Logical Residual construction uses the boundary iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/HistoryLogicalResidual.lean#L93-L100
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/HistoryLogicalResidual.lean#L93-L100

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

theorem QEC.Coding.BDL26HistoryLogicalResidual.boundary_iff (sigma : TopInput S n)
    (e u : (SuffixData S n).family.Cochain1 (TopIndex n))
    (hu : (SuffixData S n).family.coboundary1 (TopIndex n) u = sigma.val) :
    (∃ f : (SuffixData S n).family.Cochain0 (TopIndex n),
      (SuffixData S n).family.coboundary0 (TopIndex n) f = topWord S n sigma e) ↔
      ∃ f : (SuffixData S n).family.Cochain0 0,
        (SuffixData S n).family.coboundary0 0 f = lowerWord S n sigma e u := by sorry
