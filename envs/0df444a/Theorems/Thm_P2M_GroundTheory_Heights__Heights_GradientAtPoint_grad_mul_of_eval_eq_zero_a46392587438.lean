-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_GradientAtPoint_grad_mul_of_eval_eq_zero_a46392587438
-- name    : P2M_GroundTheory_Heights__Heights_GradientAtPoint_grad_mul_of_eval_eq_zero_a46392587438
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T04:07:40.181028+00:00
-- url     : https://prove2.me/theorems/388da8e4-e2ef-46fe-919e-e1858ac58a8a
-- title:
--   P2 M Ground Theory Heights  Heights Gradient At Point grad mul of eval eq zero a46392587438: P2 M Ground Theory Heights  Heights Gradient At Point grad mul of eval eq zero a46392587438
-- statement:
--   The P2 M Ground Theory Heights  Heights Gradient At Point grad mul of eval eq zero a46392587438 construction uses the P2 M Ground Theory Heights  Heights Gradient At Point grad mul of eval eq zero a46392587438 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/GradientAtPoint.lean#L36-L38
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/GradientAtPoint.lean#L36-L38

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

theorem P2M_GroundTheory_Heights__Heights_GradientAtPoint_grad_mul_of_eval_eq_zero_a46392587438 (r p : MvPolynomial σ ℂ) (hp : eval w p = 0) :
    grad w (r * p) = eval w r • grad w p := by sorry

alias «GroundTheory».«Heights₂».«Heights».«GradientAtPoint».«grad_mul_of_eval_eq_zero» := P2M_GroundTheory_Heights__Heights_GradientAtPoint_grad_mul_of_eval_eq_zero_a46392587438
