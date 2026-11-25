-- Prove2me | Theorems.Thm_PI_AddIntG_Wk_thirdRoot_sub_var_zero_ne_zero
-- name    : PI.AddIntG.Wk.thirdRoot_sub_var_zero_ne_zero
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T05:22:53.153802+00:00
-- url     : https://prove2.me/theorems/aceef58f-9295-5d86-9019-bc1b1080e07d
-- title:
--   Wk: third Root sub var zero ne zero
-- statement:
--   The Wk construction uses the third Root sub var zero ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdditiveIntegralGroups/ThirdRootSubVarZeroNeZero.lean#L235-L241
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdditiveIntegralGroups/ThirdRootSubVarZeroNeZero.lean#L235-L241

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdditiveIntegralGroups_CoeffWSeriesVarZero
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdditiveIntegralGroups_SubstMem
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdditiveIntegralGroups_ThirdRootSubVarZeroNeZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Classical
open PI PI.AddIntG PI.AddIntG.Wk
variable {p : ℕ} [Fact p.Prime]

theorem PI.AddIntG.Wk.thirdRoot_sub_var_zero_ne_zero (W : WeierstrassCurve ℂ_[p]) (wq : PowerSeries ℂ_[p]) : Z3 W wq - Xv 0 ≠ 0 := by sorry
