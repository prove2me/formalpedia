-- Prove2me | Theorems.Thm_PI_FglTriFactor_Wk_upd_ne
-- name    : PI.FglTriFactor.Wk.upd_ne
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:51:03.427112+00:00
-- url     : https://prove2.me/theorems/8d09614e-269f-4472-8634-bff43bb9e0f3
-- title:
--   Wk: upd ne
-- statement:
--   The Wk construction uses the upd ne property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FormalGroupTriangles/CoeffSubstUpdZero.lean#L28-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FormalGroupTriangles/CoeffSubstUpdZero.lean#L28-L29

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

theorem PI.FglTriFactor.Wk.upd_ne {k i : σ} (t : MvPowerSeries σ K) (h : i ≠ k) : upd k t i = MvPowerSeries.X i := by sorry
