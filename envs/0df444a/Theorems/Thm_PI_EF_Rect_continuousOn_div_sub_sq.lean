-- Prove2me | Theorems.Thm_PI_EF_Rect_continuousOn_div_sub_sq
-- name    : PI.EF.Rect.continuousOn_div_sub_sq
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T05:28:29.755461+00:00
-- url     : https://prove2.me/theorems/0a37f3e4-2161-4720-aa9c-7c1de35b6df2
-- title:
--   Rect: continuous On div sub sq
-- statement:
--   The Rect construction uses the continuous On div sub sq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ExplicitFormula/RectIntEqZeroOfDifferentiableOn.lean#L265-L269
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ExplicitFormula/RectIntEqZeroOfDifferentiableOn.lean#L265-L269

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

theorem PI.EF.Rect.continuousOn_div_sub_sq {h : ℂ → ℂ} {z w p : ℂ} (hp : p ∈ rectOpen z w)
    (hh : ContinuousOn h (rectBdry z w)) :
    ContinuousOn (fun s => h s / (s - p) ^ 2) (rectBdry z w) := by sorry
