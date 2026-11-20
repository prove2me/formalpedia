-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXQEdgePairTransport_window_potential
-- name    : QEC.Coding.BDL26RXQEdgePairTransport.window_potential
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T07:25:53.691732+00:00
-- url     : https://prove2.me/theorems/f0968081-264b-4f61-8574-3308f6555973
-- title:
--   BDL26 RXQEdge Pair Transport: window potential
-- statement:
--   Every original correction interval and the literal adjacent pair of Phi.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/RXQEdgePairTransport.lean#L245-L251
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/RXQEdgePairTransport.lean#L245-L251

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_HigherRXFaceTower
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_RZLocalEdgeTower
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_RXQEdgePairTransport
import Theorems.Thm_QEC_Locality_NoEdgeBetween_symm

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26RXQEdgePairTransport
open MultiscaleDecoder BDL26FiniteAlternatingCore BDL26FiniteTannerSquare BDL26DecodingGraph
open BDL26IndexedDecoder BDL26HistorySyndromeSensitivity BDL26HistoryErrorTelescoping
open BDL26LocalizedHistoryErrorDescent BDL26CSSHamiltonian BDL26ActualFailureReadout
open BDL26RZMap1CoordinateBridge BDL26RXLocalReplacement BDL26RZLocalReplacement
open BDL26OwnerIncidenceMasks BDL26HistoryLogicalResidual BDL26TannerLocalRegularity
open scoped Classical BigOperators

theorem QEC.Coding.BDL26RXQEdgePairTransport.window_potential (S : OddScale) (N : Nat) (sigma tau : TopInput S N)
    (top : LocalizedWord S N sigma tau (TopIndex N)) (j : Nat) (hN : 2*j+3≤N) :
    intervalPotential S N sigma tau top (rzIndex N j hN).castSucc (rxIndex N j hN).succ=
      edgePotential S N sigma tau top (rxIndex N j hN)+
        ((SuffixData S N).selectedMap (rxIndex N j hN)).map0
          ((index_pair N j hN).symm ▸ edgePotential S N sigma tau top (rzIndex N j hN)) := by sorry
