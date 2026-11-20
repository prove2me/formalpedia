-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXQEdgePairTransport_owner_ambient
-- name    : QEC.Coding.BDL26RXQEdgePairTransport.owner_ambient
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T07:30:28.547538+00:00
-- url     : https://prove2.me/theorems/cd76235a-b91a-4b38-bc4e-6c8a4bc2dfa1
-- title:
--   BDL26 RXQEdge Pair Transport: owner ambient
-- statement:
--   The BDL26 RXQEdge Pair Transport construction uses the owner ambient property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/RXQEdgePairTransport.lean#L133-L140
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/RXQEdgePairTransport.lean#L133-L140

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

theorem QEC.Coding.BDL26RXQEdgePairTransport.owner_ambient (S : OddScale) (N j : Nat) (hN : 2*j+3≤N)
    (q : Physical S (2*j+3))
    (e : QDoubleCylinderEdge (transposePresentation (state S (2*j+3)).presentation) q S) :
    qEdgeOwner S j q e=BDL26RZPhysicalXStarTransport.upperXChart S (N+2)
      (Edge N (rzIndex N j hN)) (rz_odd N j hN) (.inl (.inr ⟨q,e⟩)) := by sorry
