-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_projCoord_eq_projCoordRing_f401ac45dd71
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_projCoord_eq_projCoordRing_f401ac45dd71
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T04:18:40.9143+00:00
-- url     : https://prove2.me/theorems/a8f09f9a-b930-5717-8bb6-0987f0cdff73
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR proj Coord eq proj Coord Ring f401ac45dd71: P2 M Ground Theory Heights  Heights Numbers DVR proj Coord eq proj Coord Ring f401ac45dd71
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR proj Coord eq proj Coord Ring f401ac45dd71 construction uses the P2 M Ground Theory Heights  Heights Numbers DVR proj Coord eq proj Coord Ring f401ac45dd71 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PTruncSpecialize.lean#L28-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PTruncSpecialize.lean#L28-L32

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

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_projCoord_eq_projCoordRing_f401ac45dd71 {Φ : Type*} [Field Φ] [Algebra Ω Φ] (y : (Σ k, ι k) → Ω)
    (w : Module.Basis (Fin N) Ω E) (φ : Fin M → Module.Dual Ω E) (t : Fin N → Φ) :
    projCoord y w φ t = projCoordRing y w φ t := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«projCoord_eq_projCoordRing» := P2M_GroundTheory_Heights__Heights_NumbersDVR_projCoord_eq_projCoordRing_f401ac45dd71
