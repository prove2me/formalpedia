-- Prove2me | Theorems.Thm_PI_FglTriFactor_Wk_upd_mem
-- name    : PI.FglTriFactor.Wk.upd_mem
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T05:30:04.059568+00:00
-- url     : https://prove2.me/theorems/df6cd0d7-0eb3-4125-af3f-65967ade727f
-- title:
--   Wk: upd mem
-- statement:
--   The Wk construction uses the upd mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FormalGroupTriangles/CoeffSubstUpdZero.lean#L39-L43
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FormalGroupTriangles/CoeffSubstUpdZero.lean#L39-L43

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

theorem PI.FglTriFactor.Wk.upd_mem {S : Subring K} (k : σ) {t : MvPowerSeries σ K} (ht : t ∈ SerS S σ) (i : σ) :
    upd k t i ∈ SerS S σ := by sorry
