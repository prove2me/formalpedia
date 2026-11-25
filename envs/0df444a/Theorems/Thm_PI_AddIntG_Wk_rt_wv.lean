-- Prove2me | Theorems.Thm_PI_AddIntG_Wk_rt_wv
-- name    : PI.AddIntG.Wk.rt_wv
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T05:23:09.488559+00:00
-- url     : https://prove2.me/theorems/67f1c816-dba9-53c3-b5bf-2ee488f8ebb4
-- title:
--   Wk: rt wv
-- statement:
--   The Wk construction uses the rt wv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdditiveIntegralGroups/ThirdRootSubVarZeroNeZero.lean#L78-L84
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdditiveIntegralGroups/ThirdRootSubVarZeroNeZero.lean#L78-L84

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

theorem PI.AddIntG.Wk.rt_wv (wq : PowerSeries ℂ_[p]) (i : Fin 2) :
    wv wq i = (Xv i) ^ 3 * PowerSeries.subst (Xv i : MvPowerSeries (Fin 2) ℂ_[p]) wq := by sorry
