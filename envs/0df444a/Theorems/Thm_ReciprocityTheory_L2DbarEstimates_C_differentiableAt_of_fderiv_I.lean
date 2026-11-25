-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_C_differentiableAt_of_fderiv_I
-- name    : ReciprocityTheory.L2DbarEstimates.C.differentiableAt_of_fderiv_I
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T10:54:28.001797+00:00
-- url     : https://prove2.me/theorems/4641da6e-6113-4063-a328-f24cf630e2a8
-- title:
--   C: differentiable At of fderiv I
-- statement:
--   The C construction uses the differentiable At of fderiv I property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/WeakHolomorphy/RegConv.lean#L53-L65
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/WeakHolomorphy/RegConv.lean#L53-L65

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_WeakHolomorphy_IntegralBumpProfOnePos
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_WeakHolomorphy_RegConv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.C
open MeasureTheory Metric Set Filter Topology Complex
open scoped ENNReal

theorem ReciprocityTheory.L2DbarEstimates.C.differentiableAt_of_fderiv_I {n : ℕ} {f : V n → ℂ} {x : V n}
    (hf : DifferentiableAt ℝ f x)
    (h : ∀ v, fderiv ℝ f x (I • v) = I * fderiv ℝ f x v) : DifferentiableAt ℂ f x := by sorry
