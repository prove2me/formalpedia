-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_GradientAtPoint_eval_linPart_0d7a1dbc4716
-- name    : P2M_GroundTheory_Heights__Heights_GradientAtPoint_eval_linPart_0d7a1dbc4716
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T13:13:44.391513+00:00
-- url     : https://prove2.me/theorems/189cbf78-3dd8-4844-b1ae-4eb8899ad99e
-- title:
--   P2 M Ground Theory Heights  Heights Gradient At Point eval lin Part 0d7a1dbc4716: P2 M Ground Theory Heights  Heights Gradient At Point eval lin Part 0d7a1dbc4716
-- statement:
--   The P2 M Ground Theory Heights  Heights Gradient At Point eval lin Part 0d7a1dbc4716 construction uses the P2 M Ground Theory Heights  Heights Gradient At Point eval lin Part 0d7a1dbc4716 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/GradientAtPoint.lean#L43-L44
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/GradientAtPoint.lean#L43-L44

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

theorem P2M_GroundTheory_Heights__Heights_GradientAtPoint_eval_linPart_0d7a1dbc4716 [Fintype σ] (c : σ → ℂ) : eval w (linPart w c) = 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«GradientAtPoint».«eval_linPart» := P2M_GroundTheory_Heights__Heights_GradientAtPoint_eval_linPart_0d7a1dbc4716
