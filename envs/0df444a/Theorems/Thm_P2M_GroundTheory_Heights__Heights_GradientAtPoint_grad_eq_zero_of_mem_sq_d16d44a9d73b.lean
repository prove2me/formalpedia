-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_GradientAtPoint_grad_eq_zero_of_mem_sq_d16d44a9d73b
-- name    : P2M_GroundTheory_Heights__Heights_GradientAtPoint_grad_eq_zero_of_mem_sq_d16d44a9d73b
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T03:18:08.281558+00:00
-- url     : https://prove2.me/theorems/e7c9a39b-a2f6-45bc-b39f-2d02fd23d763
-- title:
--   P2 M Ground Theory Heights  Heights Gradient At Point grad eq zero of mem sq d16d44a9d73b: P2 M Ground Theory Heights  Heights Gradient At Point grad eq zero of mem sq d16d44a9d73b
-- statement:
--   The P2 M Ground Theory Heights  Heights Gradient At Point grad eq zero of mem sq d16d44a9d73b construction uses the P2 M Ground Theory Heights  Heights Gradient At Point grad eq zero of mem sq d16d44a9d73b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/GradientAtPoint.lean#L83-L88
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/GradientAtPoint.lean#L83-L88

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

theorem P2M_GroundTheory_Heights__Heights_GradientAtPoint_grad_eq_zero_of_mem_sq_d16d44a9d73b {p : MvPolynomial σ ℂ}
    (hp : p ∈ RingHom.ker (eval w : MvPolynomial σ ℂ →+* ℂ) ^ 2) : grad w p = 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«GradientAtPoint».«grad_eq_zero_of_mem_sq» := P2M_GroundTheory_Heights__Heights_GradientAtPoint_grad_eq_zero_of_mem_sq_d16d44a9d73b
