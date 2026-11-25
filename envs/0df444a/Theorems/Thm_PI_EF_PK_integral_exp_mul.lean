-- Prove2me | Theorems.Thm_PI_EF_PK_integral_exp_mul
-- name    : PI.EF.PK.integral_exp_mul
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T05:28:12.255817+00:00
-- url     : https://prove2.me/theorems/8e1c12e3-abd6-5580-b056-a8f7e421d090
-- title:
--   PK: integral exp mul
-- statement:
--   The PK construction uses the integral exp mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ExplicitFormula/PerronKernelA.lean#L15-L18
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ExplicitFormula/PerronKernelA.lean#L15-L18

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExplicitFormula_GoodHeightExists
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExplicitFormula_RectInv
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExplicitFormula_PerronKernelA
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

theorem PI.EF.PK.integral_exp_mul (l a b : ℝ) (hl : l ≠ 0) :
    ∫ x in a..b, Real.exp (l * x) = (Real.exp (l * b) - Real.exp (l * a)) / l := by sorry
