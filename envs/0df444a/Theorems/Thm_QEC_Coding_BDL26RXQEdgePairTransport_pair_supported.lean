-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXQEdgePairTransport_pair_supported
-- name    : QEC.Coding.BDL26RXQEdgePairTransport.pair_supported
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T07:29:47.620197+00:00
-- url     : https://prove2.me/theorems/5a792027-8e30-4875-b27d-f954c98544f8
-- title:
--   BDL26 RXQEdge Pair Transport: pair supported
-- statement:
--   Both coefficients are derived from the original word; no scalar1 hypothesis.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/RXQEdgePairTransport.lean#L205-L242
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/RXQEdgePairTransport.lean#L205-L242

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

theorem QEC.Coding.BDL26RXQEdgePairTransport.pair_supported (S : OddScale) (N : Nat) (sigma tau : TopInput S N)
    (j : Nat) (hN : 2*j+3≤N) (a : Seed S j)
    (w : LocalizedWord S N sigma tau (rxIndex N j hN).succ)
    (hw : hammingSupport w.word ⊆ {seedPhysical S j a}) :
    hammingSupport (pairResult S N sigma tau j hN w).lower.word ⊆ {a.1} := by sorry
