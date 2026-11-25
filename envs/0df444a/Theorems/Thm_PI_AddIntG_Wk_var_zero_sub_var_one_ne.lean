-- Prove2me | Theorems.Thm_PI_AddIntG_Wk_var_zero_sub_var_one_ne
-- name    : PI.AddIntG.Wk.var_zero_sub_var_one_ne
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T05:23:21.995419+00:00
-- url     : https://prove2.me/theorems/4da505fb-6a03-48d7-b278-d1b29000cd50
-- title:
--   Wk: var zero sub var one ne
-- statement:
--   The Wk construction uses the var zero sub var one ne property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdditiveIntegralGroups/VarZeroSubVarOneNe.lean#L47-L54
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdditiveIntegralGroups/VarZeroSubVarOneNe.lean#L47-L54

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdditiveIntegralGroups_ThirdRootSubVarZeroNeZero
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdditiveIntegralGroups_DXEqDerivative
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdditiveIntegralGroups_DvCoeffMulEqZeroOfLtOrder
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdditiveIntegralGroups_VarZeroSubVarOneNe
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

theorem PI.AddIntG.Wk.var_zero_sub_var_one_ne : (Xv 0 - Xv 1 : MvPowerSeries (Fin 2) ℂ_[p]) ≠ 0 := by sorry
