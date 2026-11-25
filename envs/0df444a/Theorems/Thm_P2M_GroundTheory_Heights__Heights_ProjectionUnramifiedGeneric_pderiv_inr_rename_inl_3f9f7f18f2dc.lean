-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ProjectionUnramifiedGeneric_pderiv_inr_rename_inl_3f9f7f18f2dc
-- name    : P2M_GroundTheory_Heights__Heights_ProjectionUnramifiedGeneric_pderiv_inr_rename_inl_3f9f7f18f2dc
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T04:16:00.300142+00:00
-- url     : https://prove2.me/theorems/e8ccd4ba-1e6f-436b-bd43-5ed8f8278fd6
-- title:
--   P2 M Ground Theory Heights  Heights Projection Unramified Generic pderiv inr rename inl 3f9f7f18f2dc: P2 M Ground Theory Heights  Heights Projection Unramified Generic pderiv inr rename inl 3f9f7f18f2
-- statement:
--   The P2 M Ground Theory Heights  Heights Projection Unramified Generic pderiv inr rename inl 3f9f7f18f2dc construction uses the P2 M Ground Theory Heights  Heights Projection Unramified Generic pderiv inr rename inl 3f9f7f18f2dc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PProjectionUnramifiedGeneric.lean#L14-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PProjectionUnramifiedGeneric.lean#L14-L20

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Theta_SplitLinear_RankMinors
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StProjectionUnramifiedGeneric
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PProjectionUnramifiedGeneric
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
open MvPolynomial
noncomputable section
open GroundTheory.Heights₂.Heights.ProjectionUnramifiedGeneric

theorem P2M_GroundTheory_Heights__Heights_ProjectionUnramifiedGeneric_pderiv_inr_rename_inl_3f9f7f18f2dc {α β : Type} (b : β) (a : MvPolynomial α ℂ) :
    pderiv (Sum.inr b) (rename (Sum.inl : α → α ⊕ β) a) = 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ProjectionUnramifiedGeneric».«pderiv_inr_rename_inl» := P2M_GroundTheory_Heights__Heights_ProjectionUnramifiedGeneric_pderiv_inr_rename_inl_3f9f7f18f2dc
