-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RZPhysicalStarTransport_self_zero_potential
-- name    : QEC.Coding.BDL26RZPhysicalStarTransport.self_zero_potential
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T08:41:45.394786+00:00
-- url     : https://prove2.me/theorems/e4cc97b5-ec82-4f9c-84e3-d2e509274dfb
-- title:
--   BDL26 RZPhysical Star Transport: self zero potential
-- statement:
--   An actual zero potential satisfies all eleven physical clauses for equal inputs.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RZPhysicalStarTransport.lean#L508-L514
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RZPhysicalStarTransport.lean#L508-L514

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

theorem QEC.Coding.BDL26RZPhysicalStarTransport.self_zero_potential (u : FamilyZ S depth i.succ) (a : Upper S depth i) :
    Pullback S depth i odd (Q0 S depth i odd u) {parentZ S depth i odd u} a a 0 := by sorry
