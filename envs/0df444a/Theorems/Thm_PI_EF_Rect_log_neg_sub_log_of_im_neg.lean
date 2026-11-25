-- Prove2me | Theorems.Thm_PI_EF_Rect_log_neg_sub_log_of_im_neg
-- name    : PI.EF.Rect.log_neg_sub_log_of_im_neg
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T05:28:42.679112+00:00
-- url     : https://prove2.me/theorems/a09d5ad5-80a3-44a0-85b1-df6d96e35bea
-- title:
--   Rect: log neg sub log of im neg
-- statement:
--   The Rect construction uses the log neg sub log of im neg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ExplicitFormula/RectIntEqZeroOfDifferentiableOn.lean#L118-L122
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ExplicitFormula/RectIntEqZeroOfDifferentiableOn.lean#L118-L122

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

theorem PI.EF.Rect.log_neg_sub_log_of_im_neg {b : ℂ} (hb : b.im < 0) : Complex.log (-b) - Complex.log b = π * I := by sorry
