-- Prove2me | Theorems.Thm_PI_EF_Rect_rectInt_add
-- name    : PI.EF.Rect.rectInt_add
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T02:24:38.875801+00:00
-- url     : https://prove2.me/theorems/1db99c36-a916-41b7-b513-811776977df4
-- title:
--   Rect: rect Int add
-- statement:
--   The Rect construction uses the rect Int add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ExplicitFormula/RectIntEqZeroOfDifferentiableOn.lean#L184-L194
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ExplicitFormula/RectIntEqZeroOfDifferentiableOn.lean#L184-L194

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

theorem PI.EF.Rect.rectInt_add {f g : ℂ → ℂ} {z w : ℂ} (hf : ContinuousOn f (rectBdry z w))
    (hg : ContinuousOn g (rectBdry z w)) :
    rectInt (fun s => f s + g s) z w = rectInt f z w + rectInt g z w := by sorry
