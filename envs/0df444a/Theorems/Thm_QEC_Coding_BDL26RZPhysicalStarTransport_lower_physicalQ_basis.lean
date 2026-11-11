-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RZPhysicalStarTransport_lower_physicalQ_basis
-- name    : QEC.Coding.BDL26RZPhysicalStarTransport.lower_physicalQ_basis
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T06:26:43.484319+00:00
-- url     : https://prove2.me/theorems/57ffb2e4-aa5f-4ca3-b936-768aad05ba5f
-- title:
--   BDL26 RZPhysical Star Transport: lower physical Q basis
-- statement:
--   The lower word is the fixed original q basis, for arbitrary background a.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RZPhysicalStarTransport.lean#L373-L379
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RZPhysicalStarTransport.lean#L373-L379

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

theorem QEC.Coding.BDL26RZPhysicalStarTransport.lower_physicalQ_basis (a : Upper S depth i) (q : (Old S depth i).Q)
    (v : QDoubleCylinderVertex (transposePresentation (Old S depth i)) q S) :
    lowerError S depth i odd a (a+canonicalBasisWord (F := BDL26FiniteTannerSquare.Field) (physicalQ S depth i odd q v))=
      canonicalBasisWord (F := BDL26FiniteTannerSquare.Field) q := by sorry
