-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RZPhysicalStarTransport_add_localized
-- name    : QEC.Coding.BDL26RZPhysicalStarTransport.add_localized
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T08:43:43.063222+00:00
-- url     : https://prove2.me/theorems/682eb996-00dc-4367-ad5d-4525c68d83db
-- title:
--   BDL26 RZPhysical Star Transport: add localized
-- statement:
--   Mixed physical perturbations remain in the same actual star.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RZPhysicalStarTransport.lean#L517-L531
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RZPhysicalStarTransport.lean#L517-L531

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

theorem QEC.Coding.BDL26RZPhysicalStarTransport.add_localized (u : FamilyZ S depth i.succ) (a e f : Upper S depth i)
    (he : hammingSupport e ⊆ upperStar S depth i u)
    (hf : hammingSupport f ⊆ upperStar S depth i u) :
    Localized S depth i u a (a+(e+f)) := by sorry
