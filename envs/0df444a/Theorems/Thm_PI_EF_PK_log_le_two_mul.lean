-- Prove2me | Theorems.Thm_PI_EF_PK_log_le_two_mul
-- name    : PI.EF.PK.log_le_two_mul
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T05:27:54.607348+00:00
-- url     : https://prove2.me/theorems/e7faa3b6-8b37-47eb-92d7-dfad82808e6f
-- title:
--   PK: log le two mul
-- statement:
--   The PK construction uses the log le two mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ExplicitFormula/ContinuousInvSqrt.lean#L91-L93
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ExplicitFormula/ContinuousInvSqrt.lean#L91-L93

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExplicitFormula_PerronTruncOf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExplicitFormula_ContinuousInvSqrt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PI PI.EF PI.EF.PK
open Complex MeasureTheory intervalIntegral Real

theorem PI.EF.PK.log_le_two_mul {X Y : ℝ} (hX : 0 < X) (hXY : X ≤ Y ^ 2) : Real.log X ≤ 2 * Real.log Y := by sorry
