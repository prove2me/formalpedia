-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_isFlagFrame_scaledTriv_9910a8ec665d
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_isFlagFrame_scaledTriv_9910a8ec665d
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T04:11:28.386799+00:00
-- url     : https://prove2.me/theorems/2a244fdf-79d2-45d6-accd-492c91395de4
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR is Flag Frame scaled Triv 9910a8ec665d: P2 M Ground Theory Heights  Heights Numbers DVR is Flag Frame scaled Triv 9910a8ec665d
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR is Flag Frame scaled Triv 9910a8ec665d construction uses the P2 M Ground Theory Heights  Heights Numbers DVR is Flag Frame scaled Triv 9910a8ec665d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/BundleObjects.lean#L252-L274
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/BundleObjects.lean#L252-L274

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

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_isFlagFrame_scaledTriv_9910a8ec665d (y : (Σ k, ι k) → Ω) (r : ℕ) {s : Ω} (hs : s ≠ 0) :
    IsFlagFrame y (scaledTrivBundle R (segreVec y) r hs) (scaledBasis r hs) 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«isFlagFrame_scaledTriv» := P2M_GroundTheory_Heights__Heights_NumbersDVR_isFlagFrame_scaledTriv_9910a8ec665d
