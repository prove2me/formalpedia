-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXQEdgePairTransport_intermediate_supported
-- name    : QEC.Coding.BDL26RXQEdgePairTransport.intermediate_supported
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T07:30:18.145817+00:00
-- url     : https://prove2.me/theorems/032acb62-9fb0-48f9-81a7-35fed7675b76
-- title:
--   BDL26 RXQEdge Pair Transport: intermediate supported
-- statement:
--   The complete intermediate word lies in the literal actual Q-edge star.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/RXQEdgePairTransport.lean#L176-L202
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/RXQEdgePairTransport.lean#L176-L202

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

theorem QEC.Coding.BDL26RXQEdgePairTransport.intermediate_supported (S : OddScale) (N : Nat) (sigma tau : TopInput S N)
    (j : Nat) (hN : 2*j+3≤N) (a : Seed S j)
    (w : LocalizedWord S N sigma tau (rxIndex N j hN).succ)
    (hw : w.word=canonicalBasisWord (F:=F) (seedPhysical S j a)) :
    hammingSupport (middle S N sigma tau j hN w).word ⊆
      BDL26RXPhysicalStarTransport.physicalXStar (state S (2*j+4)).presentation
        (qEdgeOwner S j a.1 a.2.1) := by sorry
