-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_GradientAtPoint_grad_C_e893e68d7bf6
-- name    : P2M_GroundTheory_Heights__Heights_GradientAtPoint_grad_C_e893e68d7bf6
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T03:18:03.882998+00:00
-- url     : https://prove2.me/theorems/dd02e753-6846-49fe-ba26-ec376cc06127
-- title:
--   P2 M Ground Theory Heights  Heights Gradient At Point grad C e893e68d7bf6: P2 M Ground Theory Heights  Heights Gradient At Point grad C e893e68d7bf6
-- statement:
--   The P2 M Ground Theory Heights  Heights Gradient At Point grad C e893e68d7bf6 construction uses the P2 M Ground Theory Heights  Heights Gradient At Point grad C e893e68d7bf6 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/GradientAtPoint.lean#L25-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/GradientAtPoint.lean#L25-L27

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

theorem P2M_GroundTheory_Heights__Heights_GradientAtPoint_grad_C_e893e68d7bf6 (c : ℂ) : grad w (C c : MvPolynomial σ ℂ) = 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«GradientAtPoint».«grad_C» := P2M_GroundTheory_Heights__Heights_GradientAtPoint_grad_C_e893e68d7bf6
