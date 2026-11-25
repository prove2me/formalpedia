-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_GradedFrameCharacterisation_backward_52f4b24566df
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_GradedFrameCharacterisation_backward_52f4b24566df
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T03:30:05.505806+00:00
-- url     : https://prove2.me/theorems/479b89f7-b0d7-48bd-8a70-74807a675bf8
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR Graded Frame Characterisation backward 52f4b24566df: P2 M Ground Theory Heights  Heights Numbers DVR Graded Frame Characterisation backward 52f4b24566df
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR Graded Frame Characterisation backward 52f4b24566df construction uses the P2 M Ground Theory Heights  Heights Numbers DVR Graded Frame Characterisation backward 52f4b24566df property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PTwinGradedFrameIff.lean#L178-L267
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PTwinGradedFrameIff.lean#L178-L267

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_ImportsTerBis
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_ChartGlueSat
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PTwinGradedFrameIff
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
open ReciprocityTheory.ChartRestriction.G.Geo (ChartBundle chartRing)
universe u v w
open GroundTheory.Heights₂.Heights.NumbersDVR.GradedFrameCharacterisation
variable {o : Type u} [CommRing o] {Ω : Type v} [Field Ω] [Algebra o Ω] {K : Type} [Fintype K]
  {ι : K → Type} [∀ k, Fintype (ι k)] {y : (Σ k, ι k) → Ω} {N : ℕ} {E : Type w}
  [AddCommGroup E] [Module Ω E] {B : ChartBundle o (segreVec y) N E}
  {w : Module.Basis (Fin N) Ω E} {b : Fin N → K → ℤ}
omit [∀ k, Fintype (ι k)]

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_GradedFrameCharacterisation_backward_52f4b24566df (h : IndefiniteRowSideFullHecke.NumbersDVR.Bundles.IsGradedFrame o y B
      (fun i => Submodule.span Ω (w '' {j | (j : ℕ) < i})) b w) :
    IsFlagFrame y B w b := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«GradedFrameCharacterisation».«backward» := P2M_GroundTheory_Heights__Heights_NumbersDVR_GradedFrameCharacterisation_backward_52f4b24566df
