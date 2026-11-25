-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_GraphAreaHolomorphic_adjoint_comp_self_of_norm_406da87f1cbf
-- name    : P2M_GroundTheory_Heights__Heights_GraphAreaHolomorphic_adjoint_comp_self_of_norm_406da87f1cbf
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T03:18:12.029546+00:00
-- url     : https://prove2.me/theorems/54cba159-138c-4bb4-a97c-5a463188a4ae
-- title:
--   P2 M Ground Theory Heights  Heights Graph Area Holomorphic adjoint comp self of norm 406da87f1cbf: P2 M Ground Theory Heights  Heights Graph Area Holomorphic adjoint comp self of norm 406da87f1cbf
-- statement:
--   The P2 M Ground Theory Heights  Heights Graph Area Holomorphic adjoint comp self of norm 406da87f1cbf construction uses the P2 M Ground Theory Heights  Heights Graph Area Holomorphic adjoint comp self of norm 406da87f1cbf property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PGraphAreaHolomorphic.lean#L33-L46
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PGraphAreaHolomorphic.lean#L33-L46

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

theorem P2M_GroundTheory_Heights__Heights_GraphAreaHolomorphic_adjoint_comp_self_of_norm_406da87f1cbf {E H K : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup H] [InnerProductSpace ℝ H] [FiniteDimensional ℝ H]
    [NormedAddCommGroup K] [InnerProductSpace ℝ K] [FiniteDimensional ℝ K]
    (T : E →ₗ[ℝ] K) (L : E →ₗ[ℝ] H) (h : ∀ v, ‖T v‖ ^ 2 = ‖v‖ ^ 2 + ‖L v‖ ^ 2) :
    LinearMap.adjoint T ∘ₗ T = 1 + LinearMap.adjoint L ∘ₗ L := by sorry

alias «GroundTheory».«Heights₂».«Heights».«GraphAreaHolomorphic».«adjoint_comp_self_of_norm» := P2M_GroundTheory_Heights__Heights_GraphAreaHolomorphic_adjoint_comp_self_of_norm_406da87f1cbf
