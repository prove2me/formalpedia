-- Prove2me | Theorems.Thm_PI_FglTriFactor_Wk_pr_comp
-- name    : PI.FglTriFactor.Wk.pr_comp
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:53:12.568844+00:00
-- url     : https://prove2.me/theorems/d958fb2d-e4ff-41c4-8e2f-e9d7eccaaed8
-- title:
--   Wk: pr comp
-- statement:
--   The Wk construction uses the pr comp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FormalGroupTriangles/PairSubstXZero.lean#L114-L122
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FormalGroupTriangles/PairSubstXZero.lean#L114-L122

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_FglTriFactor
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FormalGroupTriangles_CoeffSubstUpdZero
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FormalGroupTriangles_PairSubstXZero
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
open PI.AddIntG.Wk (SerS mem_SerS mvsubst_mem_SerS)
variable {p : ℕ} [Fact p.Prime]
variable {τ : Type*}

theorem PI.FglTriFactor.Wk.pr_comp {υ : Type*} {b : τ → MvPowerSeries υ ℂ_[p]} (hb : MvPowerSeries.HasSubst b)
    {x y : MvPowerSeries τ ℂ_[p]} (hx : MvPowerSeries.constantCoeff x = 0)
    (hy : MvPowerSeries.constantCoeff y = 0) (f : MvPowerSeries (Fin 2) ℂ_[p]) :
    MvPowerSeries.subst b (pr x y f) = pr (MvPowerSeries.subst b x) (MvPowerSeries.subst b y) f := by sorry
