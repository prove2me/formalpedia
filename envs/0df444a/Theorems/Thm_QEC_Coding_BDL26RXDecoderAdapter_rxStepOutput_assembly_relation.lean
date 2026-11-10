-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXDecoderAdapter_rxStepOutput_assembly_relation
-- name    : QEC.Coding.BDL26RXDecoderAdapter.rxStepOutput_assembly_relation
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T05:11:55.530383+00:00
-- url     : https://prove2.me/theorems/f750759a-c27c-4ef3-a590-5c7541157ed1
-- title:
--   BDL26 RXDecoder Adapter: rx Step Output assembly relation
-- statement:
--   The BDL26 RXDecoder Adapter construction uses the rx Step Output assembly relation property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXDecoderAdapter.lean#L520-L522
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXDecoderAdapter.lean#L520-L522

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

theorem QEC.Coding.BDL26RXDecoderAdapter.rxStepOutput_assembly_relation (h : i.val % 2 = 0) :
    AssemblyStepRelation (indexedDecoderData S depth) i (rxStepOutput S depth i h) := by sorry
