-- Prove2me | Theorems.Thm_PI_FglTriFactor_Wk_liftedThirdRoot_sub_X_zero_ne_zero
-- name    : PI.FglTriFactor.Wk.liftedThirdRoot_sub_X_zero_ne_zero
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T05:30:06.445874+00:00
-- url     : https://prove2.me/theorems/9e2e2174-7f57-547f-b533-ab2b82f3dac9
-- title:
--   Wk: lifted Third Root sub X zero ne zero
-- statement:
--   The Wk construction uses the lifted Third Root sub X zero ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FormalGroupTriangles/LiftedThirdRootSubXZeroNeZero.lean#L214-L219
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FormalGroupTriangles/LiftedThirdRootSubXZeroNeZero.lean#L214-L219

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FormalGroupTriangles_PairSubstXZero
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdditiveIntegralGroups_FormalGroupLawExists
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FormalGroupTriangles_LiftedThirdRootSubXZeroNeZero
import Theorems.Thm_PI_AddIntG_Wk_mem_SerS
import Theorems.Thm_PI_AddIntG_Wk_mvsubst_mem_SerS

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.FglTriFactor PI.FglTriFactor.Wk
open PI.AddIntG.Wk (SerS mem_SerS mvsubst_mem_SerS lam nu wser wv Z3)
variable {p : ℕ} [Fact p.Prime]

theorem PI.FglTriFactor.Wk.liftedThirdRoot_sub_X_zero_ne_zero (W : WeierstrassCurve ℂ_[p]) (wq : PowerSeries ℂ_[p]) :
    s3 W wq - MvPowerSeries.X 0 ≠ 0 := by sorry
