-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_GradientAtPoint_grad_X_sub_C_9853297c8fca
-- name    : P2M_GroundTheory_Heights__Heights_GradientAtPoint_grad_X_sub_C_9853297c8fca
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T03:56:59.802188+00:00
-- url     : https://prove2.me/theorems/45a4028d-ea5b-4622-824c-e4fd130bf930
-- title:
--   P2 M Ground Theory Heights  Heights Gradient At Point grad X sub C 9853297c8fca: P2 M Ground Theory Heights  Heights Gradient At Point grad X sub C 9853297c8fca
-- statement:
--   The P2 M Ground Theory Heights  Heights Gradient At Point grad X sub C 9853297c8fca construction uses the P2 M Ground Theory Heights  Heights Gradient At Point grad X sub C 9853297c8fca property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/GradientAtPoint.lean#L29-L34
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/GradientAtPoint.lean#L29-L34

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

theorem P2M_GroundTheory_Heights__Heights_GradientAtPoint_grad_X_sub_C_9853297c8fca [DecidableEq σ] (j : σ) : grad w (X j - C (w j)) = Pi.single j 1 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«GradientAtPoint».«grad_X_sub_C» := P2M_GroundTheory_Heights__Heights_GradientAtPoint_grad_X_sub_C_9853297c8fca
