-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXDecoderAdapter_rxData_coordinates
-- name    : QEC.Coding.BDL26RXDecoderAdapter.rxData_coordinates
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T05:04:14.998482+00:00
-- url     : https://prove2.me/theorems/c8d63ec2-0fa7-43f8-b2bf-a99e75e4519a
-- title:
--   BDL26 RXDecoder Adapter: rx Data coordinates
-- statement:
--   Every region is the actual owner fibre, up to the defining successor cast.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXDecoderAdapter.lean#L868-L882
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXDecoderAdapter.lean#L868-L882

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
import Theorems.Thm_QEC_Locality_NoEdgeBetween_symm

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

theorem QEC.Coding.BDL26RXDecoderAdapter.rxData_coordinates (h : i.val % 2 = 0) :
    HEq (rxLx S depth i h).syndromeRegion (localX (state S i.val).presentation S).syndromeRegion ∧
    HEq (rxLx S depth i h).correctionRegion (localX (state S i.val).presentation S).correctionRegion ∧
    HEq (rxLq S depth i h).syndromeRegion (localQ (state S i.val).presentation S).syndromeRegion ∧
    HEq (rxLq S depth i h).correctionRegion (localQ (state S i.val).presentation S).correctionRegion ∧
    HEq (rxLz S depth i h).syndromeRegion (localZ (state S i.val).presentation S).syndromeRegion ∧
    HEq (rxLz S depth i h).correctionRegion (localZ (state S i.val).presentation S).correctionRegion ∧
    HEq (rxData S depth i h).topCenter (topCenter (state S i.val).presentation S) ∧
    HEq (correctionOwnerAt S depth i h)
      (fun p => (vertexEquiv (state S i.val).presentation).symm
        (rxCorrectionOwner (state S i.val).presentation S p)) := by sorry
