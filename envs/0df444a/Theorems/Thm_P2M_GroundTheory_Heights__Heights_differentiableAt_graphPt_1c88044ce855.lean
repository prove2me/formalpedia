-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_differentiableAt_graphPt_1c88044ce855
-- name    : P2M_GroundTheory_Heights__Heights_differentiableAt_graphPt_1c88044ce855
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T04:46:17.923288+00:00
-- url     : https://prove2.me/theorems/550c0931-858b-4d49-b9af-f64ca87b7db4
-- title:
--   P2 M Ground Theory Heights  Heights differentiable At graph Pt 1c88044ce855: P2 M Ground Theory Heights  Heights differentiable At graph Pt 1c88044ce855
-- statement:
--   The P2 M Ground Theory Heights  Heights differentiable At graph Pt 1c88044ce855 construction uses the P2 M Ground Theory Heights  Heights differentiable At graph Pt 1c88044ce855 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PProjectionFormula.lean#L23-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PProjectionFormula.lean#L23-L33

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StatementsArea
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StAreaMultiplicity
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StFrameJacobianSum
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StGraphAreaHolomorphic
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PProjectionFormula
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

theorem P2M_GroundTheory_Heights__Heights_differentiableAt_graphPt_1c88044ce855 {d m n : ℕ} (e : Fin n ≃ Fin d ⊕ Fin m)
    {F : EuclideanSpace ℂ (Fin d) → EuclideanSpace ℂ (Fin m)} {x : EuclideanSpace ℂ (Fin d)}
    (hF : DifferentiableAt ℂ F x) : DifferentiableAt ℂ (graphPt e F) x := by sorry

alias «GroundTheory».«Heights₂».«Heights».«differentiableAt_graphPt» := P2M_GroundTheory_Heights__Heights_differentiableAt_graphPt_1c88044ce855
