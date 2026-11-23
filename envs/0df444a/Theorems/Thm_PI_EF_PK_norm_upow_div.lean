-- Prove2me | Theorems.Thm_PI_EF_PK_norm_upow_div
-- name    : PI.EF.PK.norm_upow_div
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:22:36.16001+00:00
-- url     : https://prove2.me/theorems/7894e5c4-ebef-4adc-b92e-5f28eec081dc
-- title:
--   PK: norm upow div
-- statement:
--   The PK construction uses the norm upow div property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ExplicitFormula/ContinuousInvSqrt.lean#L44-L48
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ExplicitFormula/ContinuousInvSqrt.lean#L44-L48

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

theorem PI.EF.PK.norm_upow_div (u : ℝ) (hu : 1 ≤ u) (s : ℂ) (c m : ℝ) (hm : 0 < m) (hsc : s.re ≤ c)
    (hsm : m ≤ ‖s‖) : ‖(u : ℂ) ^ s / s‖ ≤ u ^ c / m := by sorry
