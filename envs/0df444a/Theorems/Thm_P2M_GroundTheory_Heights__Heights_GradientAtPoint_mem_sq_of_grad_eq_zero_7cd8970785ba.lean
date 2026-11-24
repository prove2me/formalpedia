-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_GradientAtPoint_mem_sq_of_grad_eq_zero_7cd8970785ba
-- name    : P2M_GroundTheory_Heights__Heights_GradientAtPoint_mem_sq_of_grad_eq_zero_7cd8970785ba
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T04:07:50.666016+00:00
-- url     : https://prove2.me/theorems/44c77090-7830-4b79-8869-0c071d8dbfc2
-- title:
--   P2 M Ground Theory Heights  Heights Gradient At Point mem sq of grad eq zero 7cd8970785ba: P2 M Ground Theory Heights  Heights Gradient At Point mem sq of grad eq zero 7cd8970785ba
-- statement:
--   The P2 M Ground Theory Heights  Heights Gradient At Point mem sq of grad eq zero 7cd8970785ba construction uses the P2 M Ground Theory Heights  Heights Gradient At Point mem sq of grad eq zero 7cd8970785ba property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/GradientAtPoint.lean#L108-L112
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/GradientAtPoint.lean#L108-L112

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

theorem P2M_GroundTheory_Heights__Heights_GradientAtPoint_mem_sq_of_grad_eq_zero_7cd8970785ba [Fintype σ] {p : MvPolynomial σ ℂ}
    (hp : p ∈ RingHom.ker (eval w : MvPolynomial σ ℂ →+* ℂ)) (hg : grad w p = 0) :
    p ∈ RingHom.ker (eval w : MvPolynomial σ ℂ →+* ℂ) ^ 2 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«GradientAtPoint».«mem_sq_of_grad_eq_zero» := P2M_GroundTheory_Heights__Heights_GradientAtPoint_mem_sq_of_grad_eq_zero_7cd8970785ba
