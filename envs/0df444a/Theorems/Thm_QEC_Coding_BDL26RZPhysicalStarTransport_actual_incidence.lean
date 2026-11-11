-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RZPhysicalStarTransport_actual_incidence
-- name    : QEC.Coding.BDL26RZPhysicalStarTransport.actual_incidence
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T06:35:49.745637+00:00
-- url     : https://prove2.me/theorems/59696ae7-b895-4bc3-b0a5-2c75574c1a6a
-- title:
--   BDL26 RZPhysical Star Transport: actual incidence
-- statement:
--   This is the literal qz field transported along the actual parity equality.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RZPhysicalStarTransport.lean#L138-L142
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RZPhysicalStarTransport.lean#L138-L142

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

theorem QEC.Coding.BDL26RZPhysicalStarTransport.actual_incidence (q : FamilyQ S depth i.succ) (u : FamilyZ S depth i.succ) :
    (state S (i.val+1)).presentation.qz q u=
      rzQZIncidence (Old S depth i) (state S i.val).admissible.toTannerSquareAdmissible S
        (coord1 S depth i odd q) (coord2 S depth i odd u) := by sorry
