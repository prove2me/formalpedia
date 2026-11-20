-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXQEdgePairTransport_physical_ambient
-- name    : QEC.Coding.BDL26RXQEdgePairTransport.physical_ambient
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T07:30:05.491925+00:00
-- url     : https://prove2.me/theorems/9e24a8c3-3881-4b7f-b6f5-ce551017afff
-- title:
--   BDL26 RXQEdge Pair Transport: physical ambient
-- statement:
--   The BDL26 RXQEdge Pair Transport construction uses the physical ambient property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/RXQEdgePairTransport.lean#L125-L131
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/RXQEdgePairTransport.lean#L125-L131

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

theorem QEC.Coding.BDL26RXQEdgePairTransport.physical_ambient (S : OddScale) (N j : Nat) (hN : 2*j+3≤N) (a : Seed S j) :
    seedPhysical S j a=BDL26RXDecoderAdapter.rxPhysicalQEquiv S (N+2)
      (Edge N (rxIndex N j hN)) (rx_even N j hN)
      (.inl ⟨qEdgeOwner S j a.1 a.2.1,a.2.2⟩) := by sorry
