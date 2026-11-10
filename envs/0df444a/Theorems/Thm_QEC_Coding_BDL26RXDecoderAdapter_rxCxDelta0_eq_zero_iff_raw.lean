-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXDecoderAdapter_rxCxDelta0_eq_zero_iff_raw
-- name    : QEC.Coding.BDL26RXDecoderAdapter.rxCxDelta0_eq_zero_iff_raw
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T05:16:19.903309+00:00
-- url     : https://prove2.me/theorems/1dbd6f80-7da4-42ae-bf9e-4d429f935ac8
-- title:
--   BDL26 RXDecoder Adapter: rx Cx Delta0 eq zero iff raw
-- statement:
--   Actual local gradients have precisely the literal cylinder gradient kernel.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXDecoderAdapter.lean#L1668-L1677
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXDecoderAdapter.lean#L1668-L1677

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
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26RXDecoderAdapter
open BDL26IndexedDecoder
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26RXLocalReplacement
open BDL26ReplacementSupport BDL26ReplacementCochainMaps BDL26RXStagedRestriction
open BDL26DecodingGraph BDL26AlternatingCochain MultiscaleDecoder RXCoarseGraining
open BDL26RZMap1CoordinateBridge (tannerCoboundary0 tannerCoboundary1)
open scoped Classical BigOperators
variable (S : OddScale) (depth : Nat) (i : StepIndex depth) (h : i.val % 2 = 0)

theorem QEC.Coding.BDL26RXDecoderAdapter.rxCxDelta0_eq_zero_iff_raw (x : (state S i.val).presentation.X)
    (w : Word BDL26Field (DoubleCylinderVertex (state S i.val).presentation x S)) :
    (rxContract S depth i h).rx_local_complexes.cxDelta0 x w = 0 ↔
      wordLinearMapTranspose (doubleCylinderBoundary1 (state S i.val).presentation x S) w = 0 := by sorry
