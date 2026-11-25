-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_ConeTrdegFnField_mem_fnField_of_mem_adjoin_776b36a2f92d
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_ConeTrdegFnField_mem_fnField_of_mem_adjoin_776b36a2f92d
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T03:29:56.098617+00:00
-- url     : https://prove2.me/theorems/1dd2b470-1c78-4c97-bedd-84078b3cea8d
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR Cone Trdeg Fn Field mem fn Field of mem adjoin 776b36a2f92d: P2 M Ground Theory Heights  Heights Numbers DVR Cone Trdeg Fn Field mem fn Field of mem adj
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR Cone Trdeg Fn Field mem fn Field of mem adjoin 776b36a2f92d construction uses the P2 M Ground Theory Heights  Heights Numbers DVR Cone Trdeg Fn Field mem fn Field of mem adjoin 776b36a2f92d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PConeTrdegFnField.lean#L34-L40
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PConeTrdegFnField.lean#L34-L40

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsConeTrdegFnField
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PConeTrdegFnField
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.NumbersDVR
open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Geo (MRingOver)
open IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mcMap mcIdeal fnField)
noncomputable section
variable {O : Type} [CommRing O] {Ω : Type} [Field Ω] [Algebra O Ω]
variable {K : Type} {ι : K → Type}

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_ConeTrdegFnField_mem_fnField_of_mem_adjoin_776b36a2f92d (y : (Σ k, ι k) → Ω) {a : Ω}
    (ha : a ∈ Algebra.adjoin O (fnField O y : Set Ω)) : a ∈ fnField O y := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«ConeTrdegFnField».«mem_fnField_of_mem_adjoin» := P2M_GroundTheory_Heights__Heights_NumbersDVR_ConeTrdegFnField_mem_fnField_of_mem_adjoin_776b36a2f92d
