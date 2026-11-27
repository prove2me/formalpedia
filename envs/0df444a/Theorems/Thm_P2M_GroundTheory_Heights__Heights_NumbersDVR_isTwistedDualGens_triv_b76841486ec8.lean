-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_isTwistedDualGens_triv_b76841486ec8
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_isTwistedDualGens_triv_b76841486ec8
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T13:37:11.390854+00:00
-- url     : https://prove2.me/theorems/53920ebb-a4d1-5ce7-b5a9-3791467a8e64
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR is Twisted Dual Gens triv b76841486ec8: P2 M Ground Theory Heights  Heights Numbers DVR is Twisted Dual Gens triv b76841486ec8
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR is Twisted Dual Gens triv b76841486ec8 construction uses the P2 M Ground Theory Heights  Heights Numbers DVR is Twisted Dual Gens triv b76841486ec8 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/BundleObjects.lean#L276-L289
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/BundleObjects.lean#L276-L289

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_Objects
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_Bundle
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_BundleObjects
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
variable {Ω : Type*} [Field Ω] (R : Type*) [CommRing R] [Algebra R Ω] {τ : Type*}
variable {R}
variable (R)
variable {K : Type*} [Fintype K] {ι : K → Type*}

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_isTwistedDualGens_triv_b76841486ec8 (y : (Σ k, ι k) → Ω) (r : ℕ) :
    IsTwistedDualGens y (scaledTrivBundle R (segreVec y) r one_ne_zero) 0
      (fun l : Fin r => (LinearMap.proj l : Module.Dual Ω (Fin r → Ω))) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«isTwistedDualGens_triv» := P2M_GroundTheory_Heights__Heights_NumbersDVR_isTwistedDualGens_triv_b76841486ec8
