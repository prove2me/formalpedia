-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXQEdgePairTransport_odd_ge_three
-- name    : QEC.Coding.BDL26RXQEdgePairTransport.odd_ge_three
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T07:24:00.900705+00:00
-- url     : https://prove2.me/theorems/03b24030-2648-48e6-a963-e62c38e01de9
-- title:
--   BDL26 RXQEdge Pair Transport: odd ge three
-- statement:
--   Every odd physical lower level above the stopping boundary is included.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/RXQEdgePairTransport.lean#L90-L93
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/RXQEdgePairTransport.lean#L90-L93

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

theorem QEC.Coding.BDL26RXQEdgePairTransport.odd_ge_three (m : Nat) (hm : 3 ≤ m) (ho : ¬m%2=0) :
    ∃ j : Nat, m=2*j+3 := by sorry
