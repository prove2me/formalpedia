-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Regular_RiemannExtensionSlices_cons_mem_ball_one_42c41052423a
-- name    : P2M_GroundTheory_Heights__Heights_Regular_RiemannExtensionSlices_cons_mem_ball_one_42c41052423a
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T04:17:21.659795+00:00
-- url     : https://prove2.me/theorems/e3245930-0bdc-4ad2-8440-28bd0c6127ad
-- title:
--   P2 M Ground Theory Heights  Heights Regular Riemann Extension Slices cons mem ball one 42c41052423a: P2 M Ground Theory Heights  Heights Regular Riemann Extension Slices cons mem ball one 42c41052423a
-- statement:
--   The P2 M Ground Theory Heights  Heights Regular Riemann Extension Slices cons mem ball one 42c41052423a construction uses the P2 M Ground Theory Heights  Heights Regular Riemann Extension Slices cons mem ball one 42c41052423a property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Regularisation/PRiemannExtensionSlices.lean#L32-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Regularisation/PRiemannExtensionSlices.lean#L32-L37

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_AnalyticCharts_Osgood
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_StRiemannSlices
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_PRiemannExtensionSlices
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Regular
open Complex Metric MeasureTheory Set Filter Topology ReciprocityTheory.AnForm.Osgood
open scoped Real
noncomputable section
open GroundTheory.Heights₂.Heights.Regular.RiemannExtensionSlices

theorem P2M_GroundTheory_Heights__Heights_Regular_RiemannExtensionSlices_cons_mem_ball_one_42c41052423a {n : ℕ} {x : ℂ} (hx : ‖x‖ < 1) {y : Fin n → ℂ}
    (hy : y ∈ ball (0 : Fin n → ℂ) 1) : (Fin.cons x y : Fin (n + 1) → ℂ) ∈ ball 0 1 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Regular».«RiemannExtensionSlices».«cons_mem_ball_one» := P2M_GroundTheory_Heights__Heights_Regular_RiemannExtensionSlices_cons_mem_ball_one_42c41052423a
