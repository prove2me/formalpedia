-- Prove2me | Theorems.Thm_PI_FglTriFactor_Wk_coeff_X_mul_shift
-- name    : PI.FglTriFactor.Wk.coeff_X_mul_shift
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T05:30:05.975854+00:00
-- url     : https://prove2.me/theorems/21ffaef6-9d4a-4cfc-8a99-331c852c2d76
-- title:
--   Wk: coeff X mul shift
-- statement:
--   The Wk construction uses the coeff X mul shift property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FormalGroupTriangles/CoeffSubstUpdZero.lean#L73-L75
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FormalGroupTriangles/CoeffSubstUpdZero.lean#L73-L75

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

theorem PI.FglTriFactor.Wk.coeff_X_mul_shift (k : σ) (H : MvPowerSeries σ K) (e : σ →₀ ℕ) :
    MvPowerSeries.coeff (e + Finsupp.single k 1) (MvPowerSeries.X k * H) = MvPowerSeries.coeff e H := by sorry
