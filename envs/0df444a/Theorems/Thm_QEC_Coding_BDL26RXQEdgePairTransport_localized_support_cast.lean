-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXQEdgePairTransport_localized_support_cast
-- name    : QEC.Coding.BDL26RXQEdgePairTransport.localized_support_cast
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T07:29:26.29079+00:00
-- url     : https://prove2.me/theorems/29c9332d-8b37-4f9d-8e89-8be55bc4bcd6
-- title:
--   BDL26 RXQEdge Pair Transport: localized support cast
-- statement:
--   Equality elimination moves the entire localized record and its support operation.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/RXQEdgePairTransport.lean#L76-L81
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/RXQEdgePairTransport.lean#L76-L81

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_HigherRXFaceTower
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_RZLocalEdgeTower
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_RXQEdgePairTransport
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26RXQEdgePairTransport
open MultiscaleDecoder BDL26FiniteAlternatingCore BDL26FiniteTannerSquare BDL26DecodingGraph
open BDL26IndexedDecoder BDL26HistorySyndromeSensitivity BDL26HistoryErrorTelescoping
open BDL26LocalizedHistoryErrorDescent BDL26CSSHamiltonian BDL26ActualFailureReadout
open BDL26RZMap1CoordinateBridge BDL26RXLocalReplacement BDL26RZLocalReplacement
open BDL26OwnerIncidenceMasks BDL26HistoryLogicalResidual BDL26TannerLocalRegularity
open scoped Classical BigOperators

theorem QEC.Coding.BDL26RXQEdgePairTransport.localized_support_cast {S : OddScale} {N : Nat} {sigma tau : TopInput S N}
    {a b : LevelIndex N} (hab : a=b) (w : LocalizedWord S N sigma tau a) :
    HEq (hammingSupport (cast (congrArg (LocalizedWord S N sigma tau) hab) w).word)
      (hammingSupport w.word) := by sorry
