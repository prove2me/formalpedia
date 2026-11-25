-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_LowerBoundFree_Line_cuspWeight_gauss_0ce6fe17e050
-- name    : P2M_GroundTheory_Heights__Heights_LowerBoundFree_Line_cuspWeight_gauss_0ce6fe17e050
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T13:37:19.82852+00:00
-- url     : https://prove2.me/theorems/653bebf1-f287-4cb1-9a24-618050d7950d
-- title:
--   P2 M Ground Theory Heights  Heights Lower Bound Free Line cusp Weight gauss 0ce6fe17e050: P2 M Ground Theory Heights  Heights Lower Bound Free Line cusp Weight gauss 0ce6fe17e050
-- statement:
--   The P2 M Ground Theory Heights  Heights Lower Bound Free Line cusp Weight gauss 0ce6fe17e050 construction uses the P2 M Ground Theory Heights  Heights Lower Bound Free Line cusp Weight gauss 0ce6fe17e050 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HodgeLowerBound/FrameDefinitions/EqZeroOfIsIsoSub.lean#L154-L162
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HodgeLowerBound/FrameDefinitions/EqZeroOfIsIsoSub.lean#L154-L162

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HodgeLowerBound_FrameDefinitions_IsFrameOverLine
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HodgeLowerBound_FrameDefinitions_EqZeroOfIsIsoSub
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open ReciprocityTheory.ChartRestriction.G.Geo
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
variable {II : IntersectionSystem} {Ψ : Type} [Fintype Ψ] {Ω : Type} [Field Ω] [Algebra ℚ Ω]
  {E : Ψ → Type} [∀ τ, AddCommGroup (E τ)] [∀ τ, Module Ω (E τ)]
open GroundTheory.Heights₂.Heights.LowerBoundFree.Line
open GaussianInt

theorem P2M_GroundTheory_Heights__Heights_LowerBoundFree_Line_cuspWeight_gauss_0ce6fe17e050 (II : IntersectionSystem) (hII) (z : (Σ _ : Unit, Fin 2) → ℂ) :
    (gaussCusp II hII).cuspWeight z = 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«LowerBoundFree».«Line».«cuspWeight_gauss» := P2M_GroundTheory_Heights__Heights_LowerBoundFree_Line_cuspWeight_gauss_0ce6fe17e050
