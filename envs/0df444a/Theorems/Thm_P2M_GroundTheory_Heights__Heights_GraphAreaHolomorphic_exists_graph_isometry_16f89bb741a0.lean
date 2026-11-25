-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_GraphAreaHolomorphic_exists_graph_isometry_16f89bb741a0
-- name    : P2M_GroundTheory_Heights__Heights_GraphAreaHolomorphic_exists_graph_isometry_16f89bb741a0
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T03:18:41.492823+00:00
-- url     : https://prove2.me/theorems/19ae09c7-eeb3-40be-998b-8abe74105d73
-- title:
--   P2 M Ground Theory Heights  Heights Graph Area Holomorphic exists graph isometry 16f89bb741a0: P2 M Ground Theory Heights  Heights Graph Area Holomorphic exists graph isometry 16f89bb741a0
-- statement:
--   The P2 M Ground Theory Heights  Heights Graph Area Holomorphic exists graph isometry 16f89bb741a0 construction uses the P2 M Ground Theory Heights  Heights Graph Area Holomorphic exists graph isometry 16f89bb741a0 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PGraphAreaHolomorphic.lean#L94-L130
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PGraphAreaHolomorphic.lean#L94-L130

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

theorem P2M_GroundTheory_Heights__Heights_GraphAreaHolomorphic_exists_graph_isometry_16f89bb741a0 {d m n : ℕ} {ι κ : Type*} [Fintype ι] [Fintype κ]
    (e : Fin n ≃ Fin d ⊕ Fin m) (φ : EuclideanSpace ℂ (Fin d) ≃ₗᵢ[ℝ] EuclideanSpace ℝ ι)
    (φm : EuclideanSpace ℂ (Fin m) ≃ₗᵢ[ℝ] EuclideanSpace ℝ κ) :
    ∃ ψ : EuclideanSpace ℂ (Fin n) → EuclideanSpace ℝ (ι ⊕ κ), Isometry ψ ∧
      ∀ (F : EuclideanSpace ℂ (Fin d) → EuclideanSpace ℂ (Fin m)) x,
        ψ (graphPt e F x) = WithLp.toLp 2 (Sum.elim (fun i => φ x i) (fun i => φm (F x) i)) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«GraphAreaHolomorphic».«exists_graph_isometry» := P2M_GroundTheory_Heights__Heights_GraphAreaHolomorphic_exists_graph_isometry_16f89bb741a0
