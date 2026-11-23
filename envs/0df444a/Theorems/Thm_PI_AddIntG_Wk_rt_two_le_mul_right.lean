-- Prove2me | Theorems.Thm_PI_AddIntG_Wk_rt_two_le_mul_right
-- name    : PI.AddIntG.Wk.rt_two_le_mul_right
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:13:01.050432+00:00
-- url     : https://prove2.me/theorems/47238f35-450e-4766-acf4-25bceb3adb29
-- title:
--   Wk: rt two le mul right
-- statement:
--   The Wk construction uses the rt two le mul right property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdditiveIntegralGroups/ThirdRootSubVarZeroNeZero.lean#L22-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdditiveIntegralGroups/ThirdRootSubVarZeroNeZero.lean#L22-L26

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

theorem PI.AddIntG.Wk.rt_two_le_mul_right (f g : MvPowerSeries σ ℂ_[p]) (hf : 2 ≤ f.order) : 2 ≤ (f * g).order := by sorry
