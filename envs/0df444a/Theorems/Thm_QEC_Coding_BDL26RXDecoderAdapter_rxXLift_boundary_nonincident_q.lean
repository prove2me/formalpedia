-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXDecoderAdapter_rxXLift_boundary_nonincident_q
-- name    : QEC.Coding.BDL26RXDecoderAdapter.rxXLift_boundary_nonincident_q
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T05:15:43.843091+00:00
-- url     : https://prove2.me/theorems/f367f4fd-abfd-492a-92af-1c688f4308bc
-- title:
--   BDL26 RXDecoder Adapter: rx XLift boundary nonincident q
-- statement:
--   The BDL26 RXDecoder Adapter construction uses the rx XLift boundary nonincident q property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXDecoderAdapter.lean#L1631-L1638
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXDecoderAdapter.lean#L1631-L1638

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

theorem QEC.Coding.BDL26RXDecoderAdapter.rxXLift_boundary_nonincident_q (x : (state S i.val).presentation.X)
    (q : (state S i.val).presentation.Q) (hxq : (state S i.val).presentation.xq x q ≠ true)
    (w : Word BDL26Field (DoubleCylinderVertex (state S i.val).presentation x S)) :
    restrictWordLinear ((rxLq S depth i h).correctionRegion q)
      ((indexedFamily S depth).coboundary0 i.succ
        ((rxContract S depth i h).support_decomposition.cxLift0 x w)) = 0 := by sorry
