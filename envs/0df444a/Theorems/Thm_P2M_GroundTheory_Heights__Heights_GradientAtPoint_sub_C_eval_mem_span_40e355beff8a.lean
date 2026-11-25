-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_GradientAtPoint_sub_C_eval_mem_span_40e355beff8a
-- name    : P2M_GroundTheory_Heights__Heights_GradientAtPoint_sub_C_eval_mem_span_40e355beff8a
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T03:17:53.580576+00:00
-- url     : https://prove2.me/theorems/781dd679-d4ff-500c-9cdd-ff5d9ed1dd76
-- title:
--   P2 M Ground Theory Heights  Heights Gradient At Point sub C eval mem span 40e355beff8a: P2 M Ground Theory Heights  Heights Gradient At Point sub C eval mem span 40e355beff8a
-- statement:
--   The P2 M Ground Theory Heights  Heights Gradient At Point sub C eval mem span 40e355beff8a construction uses the P2 M Ground Theory Heights  Heights Gradient At Point sub C eval mem span 40e355beff8a property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/GradientAtPoint.lean#L58-L70
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/GradientAtPoint.lean#L58-L70

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_GradientAtPoint
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
open GroundTheory.Heights₂.Heights.GradientAtPoint
variable {σ : Type*} (w : σ → ℂ)

theorem P2M_GroundTheory_Heights__Heights_GradientAtPoint_sub_C_eval_mem_span_40e355beff8a (p : MvPolynomial σ ℂ) :
    p - C (eval w p) ∈ Ideal.span (Set.range fun i => (X i - C (w i) : MvPolynomial σ ℂ)) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«GradientAtPoint».«sub_C_eval_mem_span» := P2M_GroundTheory_Heights__Heights_GradientAtPoint_sub_C_eval_mem_span_40e355beff8a
