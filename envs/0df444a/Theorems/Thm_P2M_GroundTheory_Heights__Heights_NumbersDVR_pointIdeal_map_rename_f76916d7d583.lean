-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_pointIdeal_map_rename_f76916d7d583
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_pointIdeal_map_rename_f76916d7d583
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T04:12:33.616345+00:00
-- url     : https://prove2.me/theorems/e2b39612-a2e5-40d8-a487-69256894a4ab
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR point Ideal map rename f76916d7d583: P2 M Ground Theory Heights  Heights Numbers DVR point Ideal map rename f76916d7d583
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR point Ideal map rename f76916d7d583 construction uses the P2 M Ground Theory Heights  Heights Numbers DVR point Ideal map rename f76916d7d583 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PSegreFlagClosurePullback.lean#L108-L136
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PSegreFlagClosurePullback.lean#L108-L136

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsSegreFlagClosure
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsFlagIndependence
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsPairNumberRelabel
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsVerticalDivisorJoinPullback
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsSegreFlagClosureBirational
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PFlagIndependenceAlgebra
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PSegreFlagClosurePullback
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

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_pointIdeal_map_rename_f76916d7d583 {K₁ K₂ : Type*} {ι₁ : K₁ → Type*} {ι₂ : K₂ → Type*} {R Φ : Type*} [CommRing R]
    [Field Φ] [Algebra R Φ] (e : K₁ ≃ K₂) (σ : (Σ k, ι₁ k) ≃ (Σ k, ι₂ k)) (hσ : ∀ v, (σ v).1 = e v.1)
    (y : (Σ k, ι₂ k) → Φ) : (pointIdeal R (y ∘ σ)).map (rename σ) = pointIdeal R y := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«pointIdeal_map_rename» := P2M_GroundTheory_Heights__Heights_NumbersDVR_pointIdeal_map_rename_f76916d7d583
