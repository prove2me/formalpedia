-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_GradientAtPoint_grad_linPart_42cc2f004632
-- name    : P2M_GroundTheory_Heights__Heights_GradientAtPoint_grad_linPart_42cc2f004632
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T13:13:56.802896+00:00
-- url     : https://prove2.me/theorems/ad0d0ffc-cfe2-4f4e-9288-ee4fa818f605
-- title:
--   P2 M Ground Theory Heights  Heights Gradient At Point grad lin Part 42cc2f004632: P2 M Ground Theory Heights  Heights Gradient At Point grad lin Part 42cc2f004632
-- statement:
--   The P2 M Ground Theory Heights  Heights Gradient At Point grad lin Part 42cc2f004632 construction uses the P2 M Ground Theory Heights  Heights Gradient At Point grad lin Part 42cc2f004632 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/GradientAtPoint.lean#L46-L50
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/GradientAtPoint.lean#L46-L50

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

theorem P2M_GroundTheory_Heights__Heights_GradientAtPoint_grad_linPart_42cc2f004632 [Fintype σ] (c : σ → ℂ) : grad w (linPart w c) = c := by sorry

alias «GroundTheory».«Heights₂».«Heights».«GradientAtPoint».«grad_linPart» := P2M_GroundTheory_Heights__Heights_GradientAtPoint_grad_linPart_42cc2f004632
