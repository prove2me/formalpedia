-- Prove2me | Theorems.Thm_PI_FglTriFactor_Wk_liftedThirdRoot_sub_X
-- name    : PI.FglTriFactor.Wk.liftedThirdRoot_sub_X
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T08:26:12.659024+00:00
-- url     : https://prove2.me/theorems/cf463699-7990-4622-91f2-aa83824eaf44
-- title:
--   Wk: lifted Third Root sub X
-- statement:
--   The Wk construction uses the lifted Third Root sub X property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FormalGroupTriangles/LiftedThirdRootSubXZeroNeZero.lean#L204-L212
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FormalGroupTriangles/LiftedThirdRootSubXZeroNeZero.lean#L204-L212

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

theorem PI.FglTriFactor.Wk.liftedThirdRoot_sub_X (W : WeierstrassCurve ℂ_[p]) (wq : PowerSeries ℂ_[p]) (i : Fin 2) :
    s3 W wq - MvPowerSeries.X (Fin.castSucc i) = pr (MvPowerSeries.X 0 : MvPowerSeries (Fin 3) ℂ_[p])
      (MvPowerSeries.X 1) (Z3 W wq - MvPowerSeries.X i) := by sorry
