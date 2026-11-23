-- Prove2me | Theorems.Thm_PI_FglTriFactor_Wk_pt_lg
-- name    : PI.FglTriFactor.Wk.pt_lg
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:26:17.192304+00:00
-- url     : https://prove2.me/theorems/e48fff38-8b39-4024-b7b1-f4ac355c4d46
-- title:
--   Wk: pt lg
-- statement:
--   The Wk construction uses the pt lg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FormalGroupTriangles/PairSubstXZero.lean#L74-L79
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FormalGroupTriangles/PairSubstXZero.lean#L74-L79

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
variable {l ex : PowerSeries ℂ_[p]} {σ τ : Type*}

theorem PI.FglTriFactor.Wk.pt_lg (hl0 : PowerSeries.constantCoeff l = 0) (hinv : PowerSeries.subst l ex = PowerSeries.X)
    {x : MvPowerSeries σ ℂ_[p]} (hx : MvPowerSeries.constantCoeff x = 0) : pt ex (lg l x) = x := by sorry
