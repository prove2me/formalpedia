-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_projCoordRing_map_405f3101cff5
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_projCoordRing_map_405f3101cff5
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T04:12:15.440518+00:00
-- url     : https://prove2.me/theorems/dac0f078-83ed-442f-a080-7bded36b6a1a
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR proj Coord Ring map 405f3101cff5: P2 M Ground Theory Heights  Heights Numbers DVR proj Coord Ring map 405f3101cff5
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR proj Coord Ring map 405f3101cff5 construction uses the P2 M Ground Theory Heights  Heights Numbers DVR proj Coord Ring map 405f3101cff5 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PTruncSpecialize.lean#L22-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PTruncSpecialize.lean#L22-L26

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsTruncSpecialize
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PTruncSpecialize
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
variable {K : Type*} {ι : K → Type} {Ω : Type*} [Field Ω] {N M : ℕ} {E : Type*} [AddCommGroup E]
  [Module Ω E]

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_projCoordRing_map_405f3101cff5 {B B' : Type*} [CommRing B] [Algebra Ω B] [CommRing B'] [Algebra Ω B']
    (g : B →ₐ[Ω] B') (y : (Σ k, ι k) → Ω) (w : Module.Basis (Fin N) Ω E)
    (φ : Fin M → Module.Dual Ω E) (u : Fin N → B) (p : Σ o, bundleIdx ι M o) :
    g (projCoordRing y w φ u p) = projCoordRing y w φ (g ∘ u) p := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«projCoordRing_map» := P2M_GroundTheory_Heights__Heights_NumbersDVR_projCoordRing_map_405f3101cff5
