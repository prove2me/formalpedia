-- Prove2me | Theorems.Thm_PI_FglTriFactor_Wk_prod_upd_zero
-- name    : PI.FglTriFactor.Wk.prod_upd_zero
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T05:29:58.656608+00:00
-- url     : https://prove2.me/theorems/ae7cc475-55a0-4218-8c17-4ea69ea14a0d
-- title:
--   Wk: prod upd zero
-- statement:
--   The Wk construction uses the prod upd zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FormalGroupTriangles/CoeffSubstUpdZero.lean#L45-L58
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FormalGroupTriangles/CoeffSubstUpdZero.lean#L45-L58

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

theorem PI.FglTriFactor.Wk.prod_upd_zero (k : σ) (d : σ →₀ ℕ) :
    (d.prod fun s e => (upd k (0 : MvPowerSeries σ K) s) ^ e) =
      if d k = 0 then MvPowerSeries.monomial d 1 else 0 := by sorry
