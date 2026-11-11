-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RZPhysicalStarTransport_upperStar_subset_inputBlocks
-- name    : QEC.Coding.BDL26RZPhysicalStarTransport.upperStar_subset_inputBlocks
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T06:51:36.271274+00:00
-- url     : https://prove2.me/theorems/65b7574a-552f-46d9-b9d6-84a6a14c58e4
-- title:
--   BDL26 RZPhysical Star Transport: upper Star subset input Blocks
-- statement:
--   A physical incidence star is contained in computed finite input blocks.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RZPhysicalStarTransport.lean#L191-L212
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RZPhysicalStarTransport.lean#L191-L212

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RZFiniteBlockTransport
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_GraphQuantitativeBounds
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_UniformWitness
import Mathlib.Tactic
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RZPhysicalStarTransport
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26RZPhysicalStarTransport
open BDL26FiniteAlternatingCore BDL26FiniteTannerSquare BDL26TannerLocalRegularity
open BDL26DecodingGraph BDL26IndexedDecoder BDL26RZLocalReplacement
open BDL26RZMap1CoordinateBridge BDL26ReplacementSupport BDL26ReplacementCochainMaps
open BDL26RZDecoderAdapter BDL26RZErrorPullback MultiscaleDecoder
open RZCoarseGraining RZCoarseGrainingData
open BDL26RZFiniteBlockTransport
open scoped Classical BigOperators
variable (S : OddScale) (depth : Nat) (i : StepIndex depth) (odd : ¬i.val%2=0)

theorem QEC.Coding.BDL26RZPhysicalStarTransport.upperStar_subset_inputBlocks (u : FamilyZ S depth i.succ) :
    upperStar S depth i u ⊆ inputBlocks S depth i odd
      (Q0 S depth i odd u) {parentZ S depth i odd u} := by sorry
