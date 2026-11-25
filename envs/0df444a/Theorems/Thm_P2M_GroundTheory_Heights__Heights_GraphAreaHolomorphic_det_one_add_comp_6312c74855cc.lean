-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_GraphAreaHolomorphic_det_one_add_comp_6312c74855cc
-- name    : P2M_GroundTheory_Heights__Heights_GraphAreaHolomorphic_det_one_add_comp_6312c74855cc
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T03:18:28.991272+00:00
-- url     : https://prove2.me/theorems/1b6b313a-49cf-4ae2-8772-7b93d28402ed
-- title:
--   P2 M Ground Theory Heights  Heights Graph Area Holomorphic det one add comp 6312c74855cc: P2 M Ground Theory Heights  Heights Graph Area Holomorphic det one add comp 6312c74855cc
-- statement:
--   The P2 M Ground Theory Heights  Heights Graph Area Holomorphic det one add comp 6312c74855cc construction uses the P2 M Ground Theory Heights  Heights Graph Area Holomorphic det one add comp 6312c74855cc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PGraphAreaHolomorphic.lean#L48-L57
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PGraphAreaHolomorphic.lean#L48-L57

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StatementsArea
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StAreaMultiplicity
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StGraphAreaHolomorphic
import Definitions.Def_ReciprocityTheory_AnalyticForms_AnalyticCharts_Osgood
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PGraphAreaHolomorphic
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MeasureTheory Module
open scoped ENNReal
noncomputable section
open GroundTheory.Heights₂.Heights.GraphAreaHolomorphic

theorem P2M_GroundTheory_Heights__Heights_GraphAreaHolomorphic_det_one_add_comp_6312c74855cc {E E' H : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup E'] [InnerProductSpace ℝ E'] [FiniteDimensional ℝ E']
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [FiniteDimensional ℝ H]
    (φ : E ≃ₗᵢ[ℝ] E') (L : E' →ₗ[ℝ] H) :
    LinearMap.det (1 + LinearMap.adjoint (L ∘ₗ φ.toLinearMap) ∘ₗ (L ∘ₗ φ.toLinearMap)) =
      LinearMap.det (1 + LinearMap.adjoint L ∘ₗ L) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«GraphAreaHolomorphic».«det_one_add_comp» := P2M_GroundTheory_Heights__Heights_GraphAreaHolomorphic_det_one_add_comp_6312c74855cc
