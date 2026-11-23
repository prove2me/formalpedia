-- Prove2me | Theorems.Thm_PI_FglTriFactor_Wk_hasSubst_upd
-- name    : PI.FglTriFactor.Wk.hasSubst_upd
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:53:13.444922+00:00
-- url     : https://prove2.me/theorems/2ff0ac00-0405-481e-bfd9-4c9c0a9c6a11
-- title:
--   Wk: has Subst upd
-- statement:
--   The Wk construction uses the has Subst upd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FormalGroupTriangles/CoeffSubstUpdZero.lean#L21-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FormalGroupTriangles/CoeffSubstUpdZero.lean#L21-L23

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

theorem PI.FglTriFactor.Wk.hasSubst_upd (k : σ) {t : MvPowerSeries σ K} (ht : MvPowerSeries.constantCoeff t = 0) :
    MvPowerSeries.HasSubst (upd k t) := by sorry
