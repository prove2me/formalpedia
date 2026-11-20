-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXPhysicalCoordinateTrace_rx_vertex_supported
-- name    : QEC.Coding.BDL26RXPhysicalCoordinateTrace.rx_vertex_supported
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T08:20:19.710174+00:00
-- url     : https://prove2.me/theorems/92dde714-155d-4ca6-81df-217d66fc9f55
-- title:
--   BDL26 RXPhysical Coordinate Trace: rx vertex supported
-- statement:
--   The BDL26 RXPhysical Coordinate Trace construction uses the rx vertex supported property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/RXPhysicalCoordinateTrace/Semantics.lean#L23-L48
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/RXPhysicalCoordinateTrace/Semantics.lean#L23-L48

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_RXPhysicalCoordinateTrace
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_LocalSearchFailureReduction
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_RXPhysicalCoordinateTrace_Semantics
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26RXPhysicalCoordinateTrace
open MultiscaleDecoder BDL26FiniteAlternatingCore BDL26FiniteTannerSquare BDL26DecodingGraph
open BDL26IndexedDecoder BDL26CSSHamiltonian BDL26ActualFailureReadout
open BDL26HistorySyndromeSensitivity BDL26HistoryErrorTelescoping BDL26HistoryLogicalResidual
open BDL26LocalizedHistoryErrorDescent BDL26RZMap1CoordinateBridge
open BDL26RXLocalReplacement BDL26RZLocalReplacement BDL26OwnerIncidenceMasks
open BDL26LevelTwoCode BDL26LevelTwoDistance BDL26TannerLocalRegularity
open BDL26TransposedStoppedDecoder
open scoped Classical BigOperators

theorem QEC.Coding.BDL26RXPhysicalCoordinateTrace.rx_vertex_supported (S : OddScale) (N : Nat) (sigma tau : TopInput S N)
    (i : StepIndex N) (he : (i.val+2)%2=0)
    (w : LocalizedWord S N sigma tau i.succ) (q : Physical S (i.val+2))
    (v : QDoubleCylinderVertex (state S (i.val+2)).presentation q S)
    (hw : hammingSupport w.word ⊆
      {BDL26FirstZeroQVertexTower.rxVertex S (i.val+2) he q v}) :
    (step S N sigma tau i w).potential=0 ∧
      hammingSupport (step S N sigma tau i w).lower.word ⊆ {q} := by sorry
