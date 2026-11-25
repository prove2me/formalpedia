-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_SegreFlagConeAlg_expand_coords_9a11dc23b2ee
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_SegreFlagConeAlg_expand_coords_9a11dc23b2ee
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T08:07:55.423846+00:00
-- url     : https://prove2.me/theorems/b406c3b4-f634-4d14-b830-15ce8624f6b3
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR Segre Flag Cone Alg expand coords 9a11dc23b2ee: P2 M Ground Theory Heights  Heights Numbers DVR Segre Flag Cone Alg expand coords 9a11dc23b2ee
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR Segre Flag Cone Alg expand coords 9a11dc23b2ee construction uses the P2 M Ground Theory Heights  Heights Numbers DVR Segre Flag Cone Alg expand coords 9a11dc23b2ee property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PSegreFlagConeAlg.lean#L61-L71
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PSegreFlagConeAlg.lean#L61-L71

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsSegreFlagConeAlg
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PPairConeAlg
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PSegreFlagClosureModel
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PSegreFlagConeAlg
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
open GroundTheory.Heights₂.Heights.NumbersDVR.SegreFlagConeAlg

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_SegreFlagConeAlg_expand_coords_9a11dc23b2ee {Ω : Type*} [Field Ω] {E : Type*} [AddCommGroup E] [Module Ω E] {Φ : Type*} [Field Φ]
    [Algebra Ω Φ] {n : ℕ} {σ : Type*} (u : Fin n → E) (s' : Fin n → Φ) (ψ : Module.Dual Ω E) (V : Φ)
    (hV : V = ∑ q, s' q * algebraMap Ω Φ (ψ (u q))) (Y Z : Ω) (o : σ) :
    ∑ q, C (algebraMap Ω Φ (ψ (u q) / Z)) * (C (algebraMap Ω Φ Y * s' q) * (X o : MvPolynomial σ Φ)) =
      C (algebraMap Ω Φ (Y / Z) * V) * X o := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«SegreFlagConeAlg».«expand_coords» := P2M_GroundTheory_Heights__Heights_NumbersDVR_SegreFlagConeAlg_expand_coords_9a11dc23b2ee
