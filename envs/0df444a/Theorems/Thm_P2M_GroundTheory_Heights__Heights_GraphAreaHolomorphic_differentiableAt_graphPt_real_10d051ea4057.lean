-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_GraphAreaHolomorphic_differentiableAt_graphPt_real_10d051ea4057
-- name    : P2M_GroundTheory_Heights__Heights_GraphAreaHolomorphic_differentiableAt_graphPt_real_10d051ea4057
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T01:02:51.414797+00:00
-- url     : https://prove2.me/theorems/37887155-914d-4530-83f6-85e94cea906e
-- title:
--   P2 M Ground Theory Heights  Heights Graph Area Holomorphic differentiable At graph Pt real 10d051ea4057: P2 M Ground Theory Heights  Heights Graph Area Holomorphic differentiable At graph Pt real 10d0
-- statement:
--   The P2 M Ground Theory Heights  Heights Graph Area Holomorphic differentiable At graph Pt real 10d051ea4057 construction uses the P2 M Ground Theory Heights  Heights Graph Area Holomorphic differentiable At graph Pt real 10d051ea4057 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PGraphAreaHolomorphic.lean#L59-L67
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PGraphAreaHolomorphic.lean#L59-L67

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

theorem P2M_GroundTheory_Heights__Heights_GraphAreaHolomorphic_differentiableAt_graphPt_real_10d051ea4057 {d m n : ℕ} (e : Fin n ≃ Fin d ⊕ Fin m)
    {F : EuclideanSpace ℂ (Fin d) → EuclideanSpace ℂ (Fin m)} {x : EuclideanSpace ℂ (Fin d)}
    (hF : DifferentiableAt ℝ F x) : DifferentiableAt ℝ (graphPt e F) x := by sorry

alias «GroundTheory».«Heights₂».«Heights».«GraphAreaHolomorphic».«differentiableAt_graphPt_real» := P2M_GroundTheory_Heights__Heights_GraphAreaHolomorphic_differentiableAt_graphPt_real_10d051ea4057
