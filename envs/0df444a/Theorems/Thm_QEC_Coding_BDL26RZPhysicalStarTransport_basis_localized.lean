-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RZPhysicalStarTransport_basis_localized
-- name    : QEC.Coding.BDL26RZPhysicalStarTransport.basis_localized
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T06:43:48.329951+00:00
-- url     : https://prove2.me/theorems/bf77cd27-8623-4036-8d63-8195a0b11665
-- title:
--   BDL26 RZPhysical Star Transport: basis localized
-- statement:
--   Every original actual physical basis has a support-derived endpoint.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RZPhysicalStarTransport.lean#L325-L334
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RZPhysicalStarTransport.lean#L325-L334

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

theorem QEC.Coding.BDL26RZPhysicalStarTransport.basis_localized (u : FamilyZ S depth i.succ) (q : FamilyQ S depth i.succ)
    (hq : (state S (i.val+1)).presentation.qz q u=true) (a : Upper S depth i) :
    Localized S depth i u a (a+canonicalBasisWord (F := BDL26FiniteTannerSquare.Field) q) := by sorry
