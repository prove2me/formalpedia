-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FourB_deriv_deriv_log_norm_eval_1579c03559df
-- name    : P2M_GroundTheory_Heights__Heights_FourB_deriv_deriv_log_norm_eval_1579c03559df
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T03:17:31.039796+00:00
-- url     : https://prove2.me/theorems/aac8eed6-ec36-5994-8033-1b84e7aa2df8
-- title:
--   P2 M Ground Theory Heights  Heights Four B deriv deriv log norm eval 1579c03559df: P2 M Ground Theory Heights  Heights Four B deriv deriv log norm eval 1579c03559df
-- statement:
--   The P2 M Ground Theory Heights  Heights Four B deriv deriv log norm eval 1579c03559df construction uses the P2 M Ground Theory Heights  Heights Four B deriv deriv log norm eval 1579c03559df property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/LocalDensities/LeviLine.lean#L68-L101
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/LocalDensities/LeviLine.lean#L68-L101

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_MaIntEmpty
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LocalDensities_LeviLine
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.FourB
open ReciprocityTheory.AnForm Filter Topology Polynomial
noncomputable section

theorem P2M_GroundTheory_Heights__Heights_FourB_deriv_deriv_log_norm_eval_1579c03559df (Q : ℂ[X]) (h0 : Q.coeff 0 = 1) (h1 : Q.coeff 1 = 0) :
    deriv (deriv fun t : ℝ => Real.log ‖Q.eval (t : ℂ)‖) 0 = 2 * (Q.coeff 2).re := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FourB».«deriv_deriv_log_norm_eval» := P2M_GroundTheory_Heights__Heights_FourB_deriv_deriv_log_norm_eval_1579c03559df
