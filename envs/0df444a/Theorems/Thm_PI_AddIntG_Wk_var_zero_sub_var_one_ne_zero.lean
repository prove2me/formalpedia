-- Prove2me | Theorems.Thm_PI_AddIntG_Wk_var_zero_sub_var_one_ne_zero
-- name    : PI.AddIntG.Wk.var_zero_sub_var_one_ne_zero
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T05:23:16.095259+00:00
-- url     : https://prove2.me/theorems/cd69a1ce-5d08-5671-86bb-5b3e8af060d9
-- title:
--   Wk: var zero sub var one ne zero
-- statement:
--   The Wk construction uses the var zero sub var one ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdditiveIntegralGroups/ThirdRootSubVarZeroNeZero.lean#L132-L138
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdditiveIntegralGroups/ThirdRootSubVarZeroNeZero.lean#L132-L138

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

theorem PI.AddIntG.Wk.var_zero_sub_var_one_ne_zero : (Xv 0 - Xv 1 : MvPowerSeries (Fin 2) ℂ_[p]) ≠ 0 := by sorry
