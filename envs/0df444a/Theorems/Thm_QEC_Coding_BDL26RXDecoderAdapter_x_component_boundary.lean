-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXDecoderAdapter_x_component_boundary
-- name    : QEC.Coding.BDL26RXDecoderAdapter.x_component_boundary
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T05:09:39.438608+00:00
-- url     : https://prove2.me/theorems/4d7f220e-d983-4446-a8a4-9151219ff2e8
-- title:
--   BDL26 RXDecoder Adapter: x component boundary
-- statement:
--   The X component has its local boundary and the actual outgoing X-to-Q term.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXDecoderAdapter.lean#L696-L711
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXDecoderAdapter.lean#L696-L711

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

theorem QEC.Coding.BDL26RXDecoderAdapter.x_component_boundary (h : i.val % 2 = 0)
    (sigma : (indexedFamily S depth).Cochain2 i.succ)
    (x : (state S i.val).presentation.X) :
    (indexedFamily S depth).coboundary1 i.succ (cxComponentTotal (rxData S depth i h) sigma x) =
      fun p => extendWordLinear ((rxLx S depth i h).syndromeRegion x)
        ((rxContract S depth i h).rx_local_complexes.cxDelta1 x
          (restrictWordLinear ((rxLx S depth i h).correctionRegion x)
            (cxComponentTotal (rxData S depth i h) sigma x))) p +
      (rxContract S depth i h).support_decomposition.cxFlow x
        (restrictWordLinear ((rxLx S depth i h).correctionRegion x)
          (cxComponentTotal (rxData S depth i h) sigma x)) p := by sorry
