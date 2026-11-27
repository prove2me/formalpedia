-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_GradientAtPoint_linPart_single_a0ed7288f973
-- name    : P2M_GroundTheory_Heights__Heights_GradientAtPoint_linPart_single_a0ed7288f973
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T13:13:39.052558+00:00
-- url     : https://prove2.me/theorems/5662031c-1da4-5fd8-9a04-9ae97628820e
-- title:
--   P2 M Ground Theory Heights  Heights Gradient At Point lin Part single a0ed7288f973: P2 M Ground Theory Heights  Heights Gradient At Point lin Part single a0ed7288f973
-- statement:
--   The P2 M Ground Theory Heights  Heights Gradient At Point lin Part single a0ed7288f973 construction uses the P2 M Ground Theory Heights  Heights Gradient At Point lin Part single a0ed7288f973 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/GradientAtPoint.lean#L52-L56
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/GradientAtPoint.lean#L52-L56

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

theorem P2M_GroundTheory_Heights__Heights_GradientAtPoint_linPart_single_a0ed7288f973 [Fintype σ] [DecidableEq σ] (j : σ) : linPart w (Pi.single j 1) = X j - C (w j) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«GradientAtPoint».«linPart_single» := P2M_GroundTheory_Heights__Heights_GradientAtPoint_linPart_single_a0ed7288f973
