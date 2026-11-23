-- Prove2me | Theorems.Thm_PI_FglTriFactor_Wk_lam_pr
-- name    : PI.FglTriFactor.Wk.lam_pr
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T02:56:28.825903+00:00
-- url     : https://prove2.me/theorems/05b6d694-8ff8-47c4-bc36-9d8dfc628a15
-- title:
--   Wk: lam pr
-- statement:
--   The Wk construction uses the lam pr property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FormalGroupTriangles/LiftedThirdRootSubXZeroNeZero.lean#L22-L38
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FormalGroupTriangles/LiftedThirdRootSubXZeroNeZero.lean#L22-L38

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

theorem PI.FglTriFactor.Wk.lam_pr {τ : Type*} (wq : PowerSeries ℂ_[p]) {x y : MvPowerSeries τ ℂ_[p]}
    (hx : MvPowerSeries.constantCoeff x = 0) (hy : MvPowerSeries.constantCoeff y = 0) :
    (y - x) * pr x y (lam wq) = PowerSeries.subst y (wser wq) - PowerSeries.subst x (wser wq) := by sorry
