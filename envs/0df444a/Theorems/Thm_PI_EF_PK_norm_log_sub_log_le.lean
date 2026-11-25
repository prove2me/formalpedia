-- Prove2me | Theorems.Thm_PI_EF_PK_norm_log_sub_log_le
-- name    : PI.EF.PK.norm_log_sub_log_le
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T05:28:04.147169+00:00
-- url     : https://prove2.me/theorems/a731dab8-51dc-4d84-8fc3-26e7f1ea326d
-- title:
--   PK: norm log sub log le
-- statement:
--   The PK construction uses the norm log sub log le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ExplicitFormula/PerronKernelB.lean#L8-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ExplicitFormula/PerronKernelB.lean#L8-L29

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExplicitFormula_PerronKernelA
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExplicitFormula_PerronKernelB
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

theorem PI.EF.PK.norm_log_sub_log_le (c T : ℝ) (hc : 0 < c) :
    ‖Complex.log (((c : ℂ) + (T : ℂ) * I) - 0) - Complex.log (((c : ℂ) + ((-T : ℝ) : ℂ) * I) - 0)‖ ≤ π := by sorry
