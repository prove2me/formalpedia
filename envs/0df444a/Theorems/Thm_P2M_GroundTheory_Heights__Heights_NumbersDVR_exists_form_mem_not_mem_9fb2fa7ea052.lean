-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_exists_form_mem_not_mem_9fb2fa7ea052
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_exists_form_mem_not_mem_9fb2fa7ea052
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T05:07:44.46359+00:00
-- url     : https://prove2.me/theorems/660afc5c-8dcb-42ce-90a3-ec5bfbdf87e4
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR exists form mem not mem 9fb2fa7ea052: P2 M Ground Theory Heights  Heights Numbers DVR exists form mem not mem 9fb2fa7ea052
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR exists form mem not mem 9fb2fa7ea052 construction uses the P2 M Ground Theory Heights  Heights Numbers DVR exists form mem not mem 9fb2fa7ea052 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PRepresentative.lean#L67-L71
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PRepresentative.lean#L67-L71

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_IsMultiHomogIdealSpanSingleton
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PRepresentative
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
noncomputable section
universe u
variable {K : Type*} [DecidableEq K] {ι : K → Type*} {R : Type*} [CommRing R]

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_exists_form_mem_not_mem_9fb2fa7ea052 {H H' : Ideal (MRing ι R)} (hH' : IsMultiHomogIdeal H')
    (h : ¬ H' ≤ H) : ∃ (x : MRing ι R) (e : K → ℕ), IsMultiHomog x e ∧ x ∈ H' ∧ x ∉ H := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«exists_form_mem_not_mem» := P2M_GroundTheory_Heights__Heights_NumbersDVR_exists_form_mem_not_mem_9fb2fa7ea052
