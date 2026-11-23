-- Prove2me | Theorems.Thm_PI_FglTriFactor_Wk_log_third_point_sum
-- name    : PI.FglTriFactor.Wk.log_third_point_sum
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T08:26:13.80156+00:00
-- url     : https://prove2.me/theorems/92d2c879-9353-4e31-8b68-33ee186b5bff
-- title:
--   Wk: log third point sum
-- statement:
--   The Wk construction uses the log third point sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FormalGroupTriangles/LogThirdPointSum.lean#L32-L44
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FormalGroupTriangles/LogThirdPointSum.lean#L32-L44

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FormalGroupTriangles_SubstUpdateVarTwoLiftedThirdRoot
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdditiveIntegralGroups_GlueHoldsVar
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FormalGroupTriangles_LogThirdPointSum
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

theorem PI.FglTriFactor.Wk.log_third_point_sum {τ : Type*} {W : WeierstrassCurve ℂ_[p]} {wq : PowerSeries ℂ_[p]} (h : IsWq W wq)
    {x y : MvPowerSeries τ ℂ_[p]} (hx : MvPowerSeries.constantCoeff x = 0) (hy : MvPowerSeries.constantCoeff y = 0) :
    lg (flog W wq) (pr x y (Z3 W wq)) = -lg (flog W wq) x - lg (flog W wq) y := by sorry
