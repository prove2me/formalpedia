-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RZPhysicalStarTransport_qCentre_parentZ
-- name    : QEC.Coding.BDL26RZPhysicalStarTransport.qCentre_parentZ
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T06:19:00.93748+00:00
-- url     : https://prove2.me/theorems/a0938c55-ca60-4b67-94cb-5509dee12d29
-- title:
--   BDL26 RZPhysical Star Transport: q Centre parent Z
-- statement:
--   The BDL26 RZPhysical Star Transport construction uses the q Centre parent Z property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RZPhysicalStarTransport.lean#L359-L362
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RZPhysicalStarTransport.lean#L359-L362

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

theorem QEC.Coding.BDL26RZPhysicalStarTransport.qCentre_parentZ (q : (Old S depth i).Q) (z : (Old S depth i).Z)
    (hqz : (Old S depth i).qz q z=true)
    (v : QDoubleCylinderVertex (transposePresentation (Old S depth i)) q S) :
    parentZ S depth i odd (qCentre S depth i odd q z hqz v)=z := by sorry
