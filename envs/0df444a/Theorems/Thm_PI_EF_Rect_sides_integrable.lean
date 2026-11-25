-- Prove2me | Theorems.Thm_PI_EF_Rect_sides_integrable
-- name    : PI.EF.Rect.sides_integrable
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T05:28:56.065637+00:00
-- url     : https://prove2.me/theorems/7d7ba411-2ccc-40db-842a-6f7e76ddfa0b
-- title:
--   Rect: sides integrable
-- statement:
--   The Rect construction uses the sides integrable property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ExplicitFormula/RectIntEqZeroOfDifferentiableOn.lean#L161-L174
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ExplicitFormula/RectIntEqZeroOfDifferentiableOn.lean#L161-L174

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExplicitFormula_RectIntEqZeroOfDifferentiableOn
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.EF PI.EF.Rect
open Complex MeasureTheory intervalIntegral Set Filter Topology Real

theorem PI.EF.Rect.sides_integrable {f : ℂ → ℂ} {z w : ℂ} (hf : ContinuousOn f (rectBdry z w)) :
    IntervalIntegrable (fun x : ℝ => f (x + z.im * I)) volume z.re w.re ∧
    IntervalIntegrable (fun x : ℝ => f (x + w.im * I)) volume z.re w.re ∧
    IntervalIntegrable (fun y : ℝ => f (w.re + y * I)) volume z.im w.im ∧
    IntervalIntegrable (fun y : ℝ => f (z.re + y * I)) volume z.im w.im := by sorry
