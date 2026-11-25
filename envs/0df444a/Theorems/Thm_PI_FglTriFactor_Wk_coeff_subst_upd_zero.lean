-- Prove2me | Theorems.Thm_PI_FglTriFactor_Wk_coeff_subst_upd_zero
-- name    : PI.FglTriFactor.Wk.coeff_subst_upd_zero
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T05:29:58.599974+00:00
-- url     : https://prove2.me/theorems/9148bf35-6942-4c48-9026-5f2a7a335573
-- title:
--   Wk: coeff subst upd zero
-- statement:
--   The Wk construction uses the coeff subst upd zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FormalGroupTriangles/CoeffSubstUpdZero.lean#L60-L71
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FormalGroupTriangles/CoeffSubstUpdZero.lean#L60-L71

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdditiveIntegralGroups_SubstMem
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FormalGroupTriangles_CoeffSubstUpdZero
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
variable {K : Type*} [Field K] {σ : Type*} [Finite σ] [DecidableEq σ]

theorem PI.FglTriFactor.Wk.coeff_subst_upd_zero (k : σ) (f : MvPowerSeries σ K) (m : σ →₀ ℕ) (hm : m k = 0) :
    MvPowerSeries.coeff m (MvPowerSeries.subst (upd k (0 : MvPowerSeries σ K)) f) = MvPowerSeries.coeff m f := by sorry
