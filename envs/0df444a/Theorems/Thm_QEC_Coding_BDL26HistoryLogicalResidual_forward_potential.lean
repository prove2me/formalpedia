-- Prove2me | Theorems.Thm_QEC_Coding_BDL26HistoryLogicalResidual_forward_potential
-- name    : QEC.Coding.BDL26HistoryLogicalResidual.forward_potential
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T19:07:20.493046+00:00
-- url     : https://prove2.me/theorems/3ec5d79c-8a97-44a6-bee9-3534010c65f7
-- title:
--   BDL26 History Logical Residual: forward potential
-- statement:
--   The forward witness is this entire transported f2 plus the computed Q+Q'.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/HistoryLogicalResidual.lean#L103-L112
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/HistoryLogicalResidual.lean#L103-L112

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

theorem QEC.Coding.BDL26HistoryLogicalResidual.forward_potential (sigma : TopInput S n)
    (e u : (SuffixData S n).family.Cochain1 (TopIndex n))
    (hu : (SuffixData S n).family.coboundary1 (TopIndex n) u = sigma.val)
    (f2 : (SuffixData S n).family.Cochain0 0)
    (hf2 : (SuffixData S n).family.coboundary0 0 f2 = lowerWord S n sigma e u) :
    (SuffixData S n).family.coboundary0 (TopIndex n)
        (intervalMap0 (SuffixData S n) 0 (TopIndex n) (Nat.zero_le _) f2 +
          residualPotential S n e u) = topWord S n sigma e := by sorry
