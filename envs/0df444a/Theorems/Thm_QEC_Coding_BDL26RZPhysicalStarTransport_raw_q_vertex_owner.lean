-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RZPhysicalStarTransport_raw_q_vertex_owner
-- name    : QEC.Coding.BDL26RZPhysicalStarTransport.raw_q_vertex_owner
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T07:20:37.140125+00:00
-- url     : https://prove2.me/theorems/72473ef7-075c-4dd4-8a29-01073b3b207d
-- title:
--   BDL26 RZPhysical Star Transport: raw q vertex owner
-- statement:
--   The Q-cylinder constructor projects to the original qz incidence.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RZPhysicalStarTransport.lean#L180-L188
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RZPhysicalStarTransport.lean#L180-L188

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
include odd

theorem QEC.Coding.BDL26RZPhysicalStarTransport.raw_q_vertex_owner (q : (Old S depth i).Q) (z : (Old S depth i).Z)
    (v : QDoubleCylinderVertex (transposePresentation (Old S depth i)) q S)
    (w : ZDoubleCylinderVertex (Old S depth i) z S)
    (hi : rzQZIncidence (Old S depth i) (state S i.val).admissible.toTannerSquareAdmissible S
      (.inr ⟨q,v⟩) ⟨z,w⟩=true) : (Old S depth i).qz q z=true := by sorry
