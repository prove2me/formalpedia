-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_comap_C_pointIdeal_a7cacdac11cc
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_comap_C_pointIdeal_a7cacdac11cc
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T08:14:04.424801+00:00
-- url     : https://prove2.me/theorems/173b265e-b4cc-4f56-be7a-9db78af0ce57
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR comap C point Ideal a7cacdac11cc: P2 M Ground Theory Heights  Heights Numbers DVR comap C point Ideal a7cacdac11cc
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR comap C point Ideal a7cacdac11cc construction uses the P2 M Ground Theory Heights  Heights Numbers DVR comap C point Ideal a7cacdac11cc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PSegreFlagProjSpecialDim.lean#L12-L18
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PSegreFlagProjSpecialDim.lean#L12-L18

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsSegreFlagProjSpecialDimSteps
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PDvrConeDimTrdeg
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PSegreFlagProjSpecialDim
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
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
noncomputable section

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_comap_C_pointIdeal_a7cacdac11cc {R : Type*} [CommRing R] {Φ : Type*} [Field Φ] [Algebra R Φ] {K : Type*}
    {ι : K → Type*} (h : Function.Injective (algebraMap R Φ)) (pt : (Σ k, ι k) → Φ) :
    (pointIdeal R pt).comap (C : R →+* MvPolynomial (Σ k, ι k) R) = ⊥ := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«comap_C_pointIdeal» := P2M_GroundTheory_Heights__Heights_NumbersDVR_comap_C_pointIdeal_a7cacdac11cc
