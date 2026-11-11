-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RZPhysicalStarTransport_two_run
-- name    : QEC.Coding.BDL26RZPhysicalStarTransport.two_run
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T12:05:15.072466+00:00
-- url     : https://prove2.me/theorems/437d847e-7392-4a2b-8a64-b00398167ded
-- title:
--   BDL26 RZPhysical Star Transport: two run
-- statement:
--   The literal original eleven clauses, plus computed parent and measured weight.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RZPhysicalStarTransport.lean#L299-L311
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RZPhysicalStarTransport.lean#L299-L311

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RZFiniteBlockTransport
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_GraphQuantitativeBounds
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_UniformWitness
import Mathlib.Tactic
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RZPhysicalStarTransport
import Theorems.Thm_QEC_Coding_BDL26RZErrorPullback_two_run
import Theorems.Thm_QEC_Coding_BDL26RZFiniteBlockTransport_two_run

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

theorem QEC.Coding.BDL26RZPhysicalStarTransport.two_run (above : 3 ≤ i.val) (u : FamilyZ S depth i.succ) (a b : Upper S depth i)
    (he : Localized S depth i u a b) :
    ∃ p : Potential S depth i,
      Pullback S depth i odd (Q0 S depth i odd u) {parentZ S depth i odd u} a b p ∧
      parent S (i.val+1) (Vertex.z u)=some (Vertex.z (parentZ S depth i odd u)) ∧
      HammingWeight (lowerError S depth i odd a b) ≤ 7 ∧
      (∀ x : (Old S depth i).X, ∀ copy : BDL26FiniteTannerSquare.Two, read0 S depth i odd p (.inr (x,copy))=0) := by sorry
