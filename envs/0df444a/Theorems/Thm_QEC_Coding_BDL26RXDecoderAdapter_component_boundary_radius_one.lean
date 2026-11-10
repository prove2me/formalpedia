-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXDecoderAdapter_component_boundary_radius_one
-- name    : QEC.Coding.BDL26RXDecoderAdapter.component_boundary_radius_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T05:14:38.998212+00:00
-- url     : https://prove2.me/theorems/18b69628-12fe-4fae-82a2-5dc50309b72f
-- title:
--   BDL26 RXDecoder Adapter: component boundary radius one
-- statement:
--   Component boundaries may reach an adjacent owner through the connecting flow.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXDecoderAdapter.lean#L746-L781
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXDecoderAdapter.lean#L746-L781

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

theorem QEC.Coding.BDL26RXDecoderAdapter.component_boundary_radius_one (h : i.val % 2 = 0)
    (sigma : (indexedFamily S depth).Cochain2 i.succ)
    (v : RXVertex (state S i.val).presentation.X (state S i.val).presentation.Q
      (state S i.val).presentation.Z)
    (p : FamilyZ S depth i.succ)
    (hp : (indexedFamily S depth).coboundary1 i.succ
      ((rxLocalComponents (rxData S depth i h)).component v sigma) p ≠ 0) :
    DirectedGraph.distance (rxData S depth i h).levelGraph.graph v
      ((rxData S depth i h).topCenter p) ≤ 1 := by sorry
