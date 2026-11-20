-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXQEdgePairTransport_path_cast
-- name    : QEC.Coding.BDL26RXQEdgePairTransport.path_cast
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T07:30:44.272647+00:00
-- url     : https://prove2.me/theorems/69b69c2f-cfb3-422d-8eee-91639fc704fd
-- title:
--   BDL26 RXQEdge Pair Transport: path cast
-- statement:
--   Pair recursion is an interval of the SAME original fixed-N path.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/RXQEdgePairTransport.lean#L268-L273
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/RXQEdgePairTransport.lean#L268-L273

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

theorem QEC.Coding.BDL26RXQEdgePairTransport.path_cast (S : OddScale) (N : Nat) (sigma tau : TopInput S N)
    (top : LocalizedWord S N sigma tau (TopIndex N)) {a b : LevelIndex N} (hab : a=b) :
    cast (congrArg (LocalizedWord S N sigma tau) hab) (path S N sigma tau top a)=
      path S N sigma tau top b := by sorry
