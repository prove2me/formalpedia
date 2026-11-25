-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_GradientAtPoint_sub_linPart_mem_sq_27d5d7fbb6f3
-- name    : P2M_GroundTheory_Heights__Heights_GradientAtPoint_sub_linPart_mem_sq_27d5d7fbb6f3
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T03:18:03.245609+00:00
-- url     : https://prove2.me/theorems/90c9922e-5a85-4430-a34a-64530fdbfe24
-- title:
--   P2 M Ground Theory Heights  Heights Gradient At Point sub lin Part mem sq 27d5d7fbb6f3: P2 M Ground Theory Heights  Heights Gradient At Point sub lin Part mem sq 27d5d7fbb6f3
-- statement:
--   The P2 M Ground Theory Heights  Heights Gradient At Point sub lin Part mem sq 27d5d7fbb6f3 construction uses the P2 M Ground Theory Heights  Heights Gradient At Point sub lin Part mem sq 27d5d7fbb6f3 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/GradientAtPoint.lean#L90-L106
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/GradientAtPoint.lean#L90-L106

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

theorem P2M_GroundTheory_Heights__Heights_GradientAtPoint_sub_linPart_mem_sq_27d5d7fbb6f3 [Fintype σ] {p : MvPolynomial σ ℂ}
    (hp : p ∈ RingHom.ker (eval w : MvPolynomial σ ℂ →+* ℂ)) :
    p - linPart w (grad w p) ∈ RingHom.ker (eval w : MvPolynomial σ ℂ →+* ℂ) ^ 2 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«GradientAtPoint».«sub_linPart_mem_sq» := P2M_GroundTheory_Heights__Heights_GradientAtPoint_sub_linPart_mem_sq_27d5d7fbb6f3
