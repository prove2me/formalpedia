-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_differentiable_eval_pointLocal_327219f7cdc0
-- name    : P2M_GroundTheory_Heights__Heights_differentiable_eval_pointLocal_327219f7cdc0
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:47:15.260742+00:00
-- url     : https://prove2.me/theorems/64345ad5-ead0-4918-9084-6399a4035433
-- title:
--   P2 M Ground Theory Heights  Heights differentiable eval point Local 327219f7cdc0: P2 M Ground Theory Heights  Heights differentiable eval point Local 327219f7cdc0
-- statement:
--   The P2 M Ground Theory Heights  Heights differentiable eval point Local 327219f7cdc0 construction uses the P2 M Ground Theory Heights  Heights differentiable eval point Local 327219f7cdc0 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PointLocalRingOrder.lean#L80-L85
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PointLocalRingOrder.lean#L80-L85

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StNormalModelPlace
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PointLocalRingOrder
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
open MvPolynomial Topology
noncomputable section
variable {σ : Type*}

theorem P2M_GroundTheory_Heights__Heights_differentiable_eval_pointLocal_327219f7cdc0 [Fintype σ] (q : MvPolynomial σ ℂ) :
    Differentiable ℂ fun z : σ → ℂ ↦ eval z q := by sorry

alias «GroundTheory».«Heights₂».«Heights».«differentiable_eval_pointLocal» := P2M_GroundTheory_Heights__Heights_differentiable_eval_pointLocal_327219f7cdc0
