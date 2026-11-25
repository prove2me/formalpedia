-- Prove2me | Theorems.Thm_PI_AddIntG_Wk_abel
-- name    : PI.AddIntG.Wk.abel
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:15:00.405803+00:00
-- url     : https://prove2.me/theorems/99b53634-b110-4b6c-b4aa-d3121069f0f2
-- title:
--   Wk: abel
-- statement:
--   The Wk construction uses the abel property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdditiveIntegralGroups/VarZeroSubVarOneNe.lean#L61-L157
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdditiveIntegralGroups/VarZeroSubVarOneNe.lean#L61-L157

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdditiveIntegralGroups_ThirdRootSubVarZeroNeZero
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdditiveIntegralGroups_DXEqDerivative
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdditiveIntegralGroups_DvCoeffMulEqZeroOfLtOrder
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdditiveIntegralGroups_VarZeroSubVarOneNe
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Classical
open PI PI.AddIntG PI.AddIntG.Wk
variable {p : ℕ} [Fact p.Prime]

theorem PI.AddIntG.Wk.abel {W : WeierstrassCurve ℂ_[p]} {wq : PowerSeries ℂ_[p]} (h : IsWq W wq) :
    PowerSeries.subst (Xv 0 : MvPowerSeries (Fin 2) ℂ_[p]) (flog W wq) +
      PowerSeries.subst (Xv 1 : MvPowerSeries (Fin 2) ℂ_[p]) (flog W wq) +
      PowerSeries.subst (Z3 W wq) (flog W wq) = 0 := by sorry
