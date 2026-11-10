-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXDecoderAdapter_rxPhysical_localEdge_parent_none
-- name    : QEC.Coding.BDL26RXDecoderAdapter.rxPhysical_localEdge_parent_none
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T05:10:11.800125+00:00
-- url     : https://prove2.me/theorems/c79cb5aa-1f1a-4605-95ad-4b8a0a474b14
-- title:
--   BDL26 RXDecoder Adapter: rx Physical local Edge parent none
-- statement:
--   Actual local-edge physical coordinates retain the literal absent parent.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXDecoderAdapter.lean#L1748-L1755
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXDecoderAdapter.lean#L1748-L1755

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
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26RXDecoderAdapter
open BDL26IndexedDecoder BDL26FiniteTannerSquare BDL26TannerLocalRegularity
open BDL26RXLocalReplacement BDL26ReplacementSupport BDL26DecodingGraph
open MultiscaleDecoder
variable (S : OddScale) (depth : Nat) (i : StepIndex depth) (h : i.val % 2 = 0)

theorem QEC.Coding.BDL26RXDecoderAdapter.rxPhysical_localEdge_parent_none (x : (state S i.val).presentation.X)
    (e : DoubleCylinderEdge (state S i.val).presentation x S) :
    parent S (i.val+1) (Vertex.q (rxPhysicalQEquiv S depth i h (Sum.inl ⟨x,e⟩))) =
      none := by sorry
