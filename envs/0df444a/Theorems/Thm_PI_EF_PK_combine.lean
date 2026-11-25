-- Prove2me | Theorems.Thm_PI_EF_PK_combine
-- name    : PI.EF.PK.combine
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T05:28:17.21484+00:00
-- url     : https://prove2.me/theorems/30ab006f-eaea-5543-95fb-22d92dd7e56a
-- title:
--   PK: combine
-- statement:
--   The PK construction uses the combine property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ExplicitFormula/ContinuousInvSqrt.lean#L66-L73
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ExplicitFormula/ContinuousInvSqrt.lean#L66-L73

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

theorem PI.EF.PK.combine {B Tp R Lf : ℂ} {b1 b2 b3 : ℝ} (h1 : ‖B‖ ≤ b1) (h2 : ‖Tp‖ ≤ b2) (h3 : ‖Lf‖ ≤ b3) :
    ‖B - Tp + I * R - I * Lf + -(I * R)‖ ≤ b1 + b2 + b3 := by sorry
