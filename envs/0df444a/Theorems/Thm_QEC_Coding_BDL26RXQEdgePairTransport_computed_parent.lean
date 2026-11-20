-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXQEdgePairTransport_computed_parent
-- name    : QEC.Coding.BDL26RXQEdgePairTransport.computed_parent
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T07:30:36.563396+00:00
-- url     : https://prove2.me/theorems/2cfa296d-f9aa-4c30-837d-058ad3760695
-- title:
--   BDL26 RXQEdge Pair Transport: computed parent
-- statement:
--   Incidence computes the original RX parent in the nonzero scalar branch.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/RXQEdgePairTransport.lean#L153-L173
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/RXQEdgePairTransport.lean#L153-L173

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

theorem QEC.Coding.BDL26RXQEdgePairTransport.computed_parent (S : OddScale) (N : Nat) (sigma tau : TopInput S N)
    (j : Nat) (hN : 2*j+3≤N) (a : Seed S j)
    (w : LocalizedWord S N sigma tau (rxIndex N j hN).succ)
    (hw : w.word=canonicalBasisWord (F:=F) (seedPhysical S j a)) :
    BDL26RXPhysicalStarTransport.parentX S (N+2) (Edge N (rxIndex N j hN))
      (rx_even N j hN) w.center=qEdgeOwner S j a.1 a.2.1 := by sorry
