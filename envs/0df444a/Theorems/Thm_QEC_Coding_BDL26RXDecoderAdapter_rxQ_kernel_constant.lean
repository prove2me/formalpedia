-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXDecoderAdapter_rxQ_kernel_constant
-- name    : QEC.Coding.BDL26RXDecoderAdapter.rxQ_kernel_constant
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T05:02:29.808657+00:00
-- url     : https://prove2.me/theorems/69507e77-f0d9-44e1-b9e5-63521c444ea2
-- title:
--   BDL26 RXDecoder Adapter: rx Q kernel constant
-- statement:
--   Actual connectedness, including the admissible bridge between copies.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXDecoderAdapter.lean#L966-L980
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXDecoderAdapter.lean#L966-L980

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

theorem QEC.Coding.BDL26RXDecoderAdapter.rxQ_kernel_constant (h : i.val % 2 = 0)
    (q : (state S i.val).presentation.Q)
    (w : Word BDL26Field (LocalRegionIndex ((rxLq S depth i h).correctionRegion q)))
    (hw : (rxContract S depth i h).rx_local_complexes.cqDelta1 q w = 0)
    (v : QDoubleCylinderVertex (state S i.val).presentation q S) :
    w (rxQVertexEquiv S depth i h q v) =
      w (rxQVertexEquiv S depth i h q (0, Sum.inl (Sum.inl ()))) := by sorry
