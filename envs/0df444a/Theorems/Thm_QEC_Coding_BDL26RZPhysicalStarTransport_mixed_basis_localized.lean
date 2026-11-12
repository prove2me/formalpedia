-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RZPhysicalStarTransport_mixed_basis_localized
-- name    : QEC.Coding.BDL26RZPhysicalStarTransport.mixed_basis_localized
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T12:44:28.973703+00:00
-- url     : https://prove2.me/theorems/ba5eabd6-7757-4a66-b88d-940083a114e0
-- title:
--   BDL26 RZPhysical Star Transport: mixed basis localized
-- statement:
--   Two incident coordinates may overlap or cancel; no support certificate is assumed.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RZPhysicalStarTransport.lean#L534-L543
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RZPhysicalStarTransport.lean#L534-L543

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

theorem QEC.Coding.BDL26RZPhysicalStarTransport.mixed_basis_localized (u : FamilyZ S depth i.succ)
    (r t : FamilyQ S depth i.succ)
    (hr : (state S (i.val+1)).presentation.qz r u=true)
    (ht : (state S (i.val+1)).presentation.qz t u=true) (a : Upper S depth i) :
    Localized S depth i u a
      (a+(canonicalBasisWord (F := BDL26FiniteTannerSquare.Field) r+
        canonicalBasisWord (F := BDL26FiniteTannerSquare.Field) t)) := by sorry
