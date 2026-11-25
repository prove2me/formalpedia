-- Prove2me | Theorems.Thm_PI_EF_PK_cLine_le_three
-- name    : PI.EF.PK.cLine_le_three
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T05:27:58.37607+00:00
-- url     : https://prove2.me/theorems/b44cb8a3-fae9-496b-8d34-4307d1ec33f9
-- title:
--   PK: c Line le three
-- statement:
--   The PK construction uses the c Line le three property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ExplicitFormula/ContinuousInvSqrt.lean#L75-L81
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ExplicitFormula/ContinuousInvSqrt.lean#L75-L81

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

theorem PI.EF.PK.cLine_le_three {u : ℝ} (hu : 2 ≤ u) : cLine u ≤ 3 := by sorry
