-- Prove2me | Theorems.Thm_PI_EF_PK_integral_inv_sqrt
-- name    : PI.EF.PK.integral_inv_sqrt
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T05:28:19.043179+00:00
-- url     : https://prove2.me/theorems/351d081c-282c-40ef-aea8-16dc9fe0d2a1
-- title:
--   PK: integral inv sqrt
-- statement:
--   The PK construction uses the integral inv sqrt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ExplicitFormula/ContinuousInvSqrt.lean#L20-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ExplicitFormula/ContinuousInvSqrt.lean#L20-L32

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

theorem PI.EF.PK.integral_inv_sqrt (T : ℝ) :
    ∫ t in -T..T, 2 * (√(1 + (2 * t) ^ 2))⁻¹ = 2 * Real.arsinh (2 * T) := by sorry
