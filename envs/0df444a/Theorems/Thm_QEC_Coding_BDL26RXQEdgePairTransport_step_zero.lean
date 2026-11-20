-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXQEdgePairTransport_step_zero
-- name    : QEC.Coding.BDL26RXQEdgePairTransport.step_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T07:47:38.228856+00:00
-- url     : https://prove2.me/theorems/b7f9df54-c318-4e3b-9538-8c1900572d47
-- title:
--   BDL26 RXQEdge Pair Transport: step zero
-- statement:
--   Zero original differences are propagated without reading the stored centre.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/RXQEdgePairTransport.lean#L57-L73
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/RXQEdgePairTransport.lean#L57-L73

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_HigherRXFaceTower
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_RZLocalEdgeTower
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_RXQEdgePairTransport
import Theorems.Thm_QEC_Coding_BDL26RZLocalEdgeTower_step_zero

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26RXQEdgePairTransport
open MultiscaleDecoder BDL26FiniteAlternatingCore BDL26FiniteTannerSquare BDL26DecodingGraph
open BDL26IndexedDecoder BDL26HistorySyndromeSensitivity BDL26HistoryErrorTelescoping
open BDL26LocalizedHistoryErrorDescent BDL26CSSHamiltonian BDL26ActualFailureReadout
open BDL26RZMap1CoordinateBridge BDL26RXLocalReplacement BDL26RZLocalReplacement
open BDL26OwnerIncidenceMasks BDL26HistoryLogicalResidual BDL26TannerLocalRegularity
open scoped Classical BigOperators

theorem QEC.Coding.BDL26RXQEdgePairTransport.step_zero (S : OddScale) (N : Nat) (sigma tau : TopInput S N)
    (i : StepIndex N) (w : LocalizedWord S N sigma tau i.succ) (hw : w.word=0) :
    (step S N sigma tau i w).lower.word=0 := by sorry
