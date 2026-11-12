-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RZPhysicalStarTransport_updated_eq_full
-- name    : QEC.Coding.BDL26RZPhysicalStarTransport.updated_eq_full
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T12:28:28.776737+00:00
-- url     : https://prove2.me/theorems/328f2290-d1c5-4ffa-9469-6277ad11fa26
-- title:
--   BDL26 RZPhysical Star Transport: updated eq full
-- statement:
--   This is the full updated error from the SAME two original runs.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RZPhysicalStarTransport.lean#L320-L322
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RZPhysicalStarTransport.lean#L320-L322

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

theorem QEC.Coding.BDL26RZPhysicalStarTransport.updated_eq_full (a b : Upper S depth i) :
    updated S depth i odd a b=a+b+(run S depth i odd a).correction+
      (run S depth i odd b).correction := by sorry
