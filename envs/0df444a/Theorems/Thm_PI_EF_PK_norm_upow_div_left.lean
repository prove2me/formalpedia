-- Prove2me | Theorems.Thm_PI_EF_PK_norm_upow_div_left
-- name    : PI.EF.PK.norm_upow_div_left
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T05:27:53.22044+00:00
-- url     : https://prove2.me/theorems/78d14d89-24e9-5e45-af26-17fb7a3ca8c9
-- title:
--   PK: norm upow div left
-- statement:
--   The PK construction uses the norm upow div left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ExplicitFormula/ContinuousInvSqrt.lean#L50-L64
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ExplicitFormula/ContinuousInvSqrt.lean#L50-L64

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

theorem PI.EF.PK.norm_upow_div_left (u : ℝ) (hu : 1 ≤ u) (t : ℝ) :
    ‖(u : ℂ) ^ (((-1 / 2 : ℝ) : ℂ) + t * I) / (((-1 / 2 : ℝ) : ℂ) + t * I)‖ ≤
      2 * (√(1 + (2 * t) ^ 2))⁻¹ := by sorry
