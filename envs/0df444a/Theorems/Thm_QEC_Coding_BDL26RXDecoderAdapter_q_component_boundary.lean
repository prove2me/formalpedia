-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXDecoderAdapter_q_component_boundary
-- name    : QEC.Coding.BDL26RXDecoderAdapter.q_component_boundary
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T05:09:36.602377+00:00
-- url     : https://prove2.me/theorems/451211c1-56d5-4f5c-b6b4-4f807c1ef24b
-- title:
--   BDL26 RXDecoder Adapter: q component boundary
-- statement:
--   The Q component has its local boundary and the actual outgoing Q-to-Z term.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXDecoderAdapter.lean#L715-L730
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXDecoderAdapter.lean#L715-L730

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXDecoderAdapter_Decomposition
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXDecoderAdapter_Coordinates
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXDecoderAdapter_Flow
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXDecoderAdapter_Lifts
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXDecoderAdapter_Representative
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXDecoderAdapter_Graph
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXDecoderAdapter_Sectors
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXDecoderAdapter_Induced
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXDecoderAdapter_Budgets
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXDecoderAdapter_LocalComplexes
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_IndexedDecoder
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXDecoderAdapter
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RXDecoderAdapter
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26RXLocalReplacement
open BDL26ReplacementSupport BDL26ReplacementCochainMaps BDL26RXStagedRestriction
open BDL26DecodingGraph BDL26AlternatingCochain MultiscaleDecoder RXCoarseGraining
open BDL26RZMap1CoordinateBridge (tannerCoboundary0 tannerCoboundary1)
open scoped Classical BigOperators
open BDL26IndexedDecoder BDL26AlternatingCochain
variable (S : OddScale) (depth : Nat) (i : StepIndex depth)
open RXCoarseGrainingData

theorem QEC.Coding.BDL26RXDecoderAdapter.q_component_boundary (h : i.val % 2 = 0)
    (sigma : (indexedFamily S depth).Cochain2 i.succ)
    (q : (state S i.val).presentation.Q) :
    (indexedFamily S depth).coboundary1 i.succ (cqComponentTotal (rxData S depth i h) sigma q) =
      fun p => extendWordLinear ((rxLq S depth i h).syndromeRegion q)
        ((rxContract S depth i h).rx_local_complexes.cqDelta1 q
          (restrictWordLinear ((rxLq S depth i h).correctionRegion q)
            (cqComponentTotal (rxData S depth i h) sigma q))) p +
      (rxContract S depth i h).support_decomposition.cqFlow q
        (restrictWordLinear ((rxLq S depth i h).correctionRegion q)
          (cqComponentTotal (rxData S depth i h) sigma q)) p := by sorry
