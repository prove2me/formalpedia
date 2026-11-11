-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RZPhysicalStarTransport_oldX_zero
-- name    : QEC.Coding.BDL26RZPhysicalStarTransport.oldX_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T07:19:57.444413+00:00
-- url     : https://prove2.me/theorems/18d8c3a8-a080-4022-9501-22587cdf1bcd
-- title:
--   BDL26 RZPhysical Star Transport: old X zero
-- statement:
--   Both copy tags vanish on the SAME full potential in a physical pullback.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RZPhysicalStarTransport.lean#L314-L317
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RZPhysicalStarTransport.lean#L314-L317

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

theorem QEC.Coding.BDL26RZPhysicalStarTransport.oldX_zero (u : FamilyZ S depth i.succ) (a b : Upper S depth i) (p : Potential S depth i)
    (hp : Pullback S depth i odd (Q0 S depth i odd u) {parentZ S depth i odd u} a b p)
    (x : (Old S depth i).X) (copy : BDL26FiniteTannerSquare.Two) : read0 S depth i odd p (.inr (x,copy))=0 := by sorry
