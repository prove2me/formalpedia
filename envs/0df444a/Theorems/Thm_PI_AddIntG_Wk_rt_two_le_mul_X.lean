-- Prove2me | Theorems.Thm_PI_AddIntG_Wk_rt_two_le_mul_X
-- name    : PI.AddIntG.Wk.rt_two_le_mul_X
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T05:22:39.553656+00:00
-- url     : https://prove2.me/theorems/67a100bf-aea2-4e31-a39d-de6c01d68aa3
-- title:
--   Wk: rt two le mul X
-- statement:
--   The Wk construction uses the rt two le mul X property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdditiveIntegralGroups/ThirdRootSubVarZeroNeZero.lean#L49-L57
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdditiveIntegralGroups/ThirdRootSubVarZeroNeZero.lean#L49-L57

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
variable {σ : Type*}

theorem PI.AddIntG.Wk.rt_two_le_mul_X {f : MvPowerSeries σ ℂ_[p]} (hf : 1 ≤ f.order) (i : σ) :
    2 ≤ (f * Xv i).order := by sorry
