-- Prove2me | Theorems.Thm_QEC_Coding_BDL26HistoryLogicalResidual_full_identity
-- name    : QEC.Coding.BDL26HistoryLogicalResidual.full_identity
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T13:41:58.738664+00:00
-- url     : https://prove2.me/theorems/bd48f996-06b3-495a-979c-ee97426ee951
-- title:
--   BDL26 History Logical Residual: full identity
-- statement:
--   The full identity for this caller's u, with the entire exact Q(u)+Q(u+e).
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/HistoryLogicalResidual/Words.lean#L93-L114
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/HistoryLogicalResidual/Words.lean#L93-L114

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

theorem QEC.Coding.BDL26HistoryLogicalResidual.full_identity (sigma : TopInput S n)
    (e u : (SuffixData S n).family.Cochain1 (TopIndex n))
    (hu : (SuffixData S n).family.coboundary1 (TopIndex n) u = sigma.val) :
    topWord S n sigma e =
      intervalMap1 (SuffixData S n) 0 (TopIndex n) (Nat.zero_le _) (lowerWord S n sigma e u) +
        (SuffixData S n).family.coboundary0 (TopIndex n) (residualPotential S n e u) := by sorry
