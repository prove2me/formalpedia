-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXQEdgePairTransport_pair_original_steps
-- name    : QEC.Coding.BDL26RXQEdgePairTransport.pair_original_steps
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T07:30:13.639835+00:00
-- url     : https://prove2.me/theorems/327e87bf-4506-49b4-9986-8375dbe89caf
-- title:
--   BDL26 RXQEdge Pair Transport: pair original steps
-- statement:
--   The BDL26 RXQEdge Pair Transport construction uses the pair original steps property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/RXQEdgePairTransport.lean#L275-L286
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/RXQEdgePairTransport.lean#L275-L286

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

theorem QEC.Coding.BDL26RXQEdgePairTransport.pair_original_steps (S : OddScale) (N : Nat) (sigma tau : TopInput S N)
    (j : Nat) (hN : 2*j+3≤N)
    (w : LocalizedWord S N sigma tau (rxIndex N j hN).succ) :
    (pairResult S N sigma tau j hN w).lower=
      (step S N sigma tau (rzIndex N j hN)
        (step S N sigma tau (rxIndex N j hN) w).lower).lower := by sorry
