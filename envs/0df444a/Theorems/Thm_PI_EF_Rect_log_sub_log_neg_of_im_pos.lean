-- Prove2me | Theorems.Thm_PI_EF_Rect_log_sub_log_neg_of_im_pos
-- name    : PI.EF.Rect.log_sub_log_neg_of_im_pos
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T05:28:40.095892+00:00
-- url     : https://prove2.me/theorems/158fe25f-3c32-4980-bad5-da42ef7a5b02
-- title:
--   Rect: log sub log neg of im pos
-- statement:
--   The Rect construction uses the log sub log neg of im pos property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ExplicitFormula/RectIntEqZeroOfDifferentiableOn.lean#L112-L116
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ExplicitFormula/RectIntEqZeroOfDifferentiableOn.lean#L112-L116

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

theorem PI.EF.Rect.log_sub_log_neg_of_im_pos {a : ℂ} (ha : 0 < a.im) : Complex.log a - Complex.log (-a) = π * I := by sorry
