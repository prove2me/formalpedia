-- Prove2me | Theorems.Thm_PI_EF_Rect_rectInt_div_sub_sq
-- name    : PI.EF.Rect.rectInt_div_sub_sq
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T05:28:48.339185+00:00
-- url     : https://prove2.me/theorems/87e810be-e613-4260-bc60-8ccb6279a7c6
-- title:
--   Rect: rect Int div sub sq
-- statement:
--   The Rect construction uses the rect Int div sub sq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ExplicitFormula/RectIntEqZeroOfDifferentiableOn.lean#L310-L331
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ExplicitFormula/RectIntEqZeroOfDifferentiableOn.lean#L310-L331

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

theorem PI.EF.Rect.rectInt_div_sub_sq {h : ℂ → ℂ} {z w p : ℂ} (hp : p ∈ rectOpen z w)
    (hh : DifferentiableOn ℂ h (rectClosed z w)) :
    rectInt (fun s => h s / (s - p) ^ 2) z w = 2 * π * I * deriv h p := by sorry
