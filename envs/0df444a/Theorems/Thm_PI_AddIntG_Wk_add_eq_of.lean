-- Prove2me | Theorems.Thm_PI_AddIntG_Wk_add_eq_of
-- name    : PI.AddIntG.Wk.add_eq_of
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T05:21:42.261682+00:00
-- url     : https://prove2.me/theorems/25396154-4914-4550-9436-b19328e68930
-- title:
--   Wk: add eq of
-- statement:
--   The Wk construction uses the add eq of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdditiveIntegralGroups/GlueHoldsVar.lean#L208-L221
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdditiveIntegralGroups/GlueHoldsVar.lean#L208-L221

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdditiveIntegralGroups_GuLine
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdditiveIntegralGroups_GlueHoldsVar
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

theorem PI.AddIntG.Wk.add_eq_of {W : WeierstrassCurve ℂ_[p]} {wq ex : PowerSeries ℂ_[p]} (h : IsWq W wq)
    (hex0 : PowerSeries.constantCoeff ex = 0) (hex : PowerSeries.subst ex (flog W wq) = PowerSeries.X)
    (F : MvPowerSeries (Fin 2) ℂ_[p]) (hF0 : MvPowerSeries.constantCoeff F = 0)
    (hF : PowerSeries.subst F (flog W wq) =
      PowerSeries.subst (Xv 0 : MvPowerSeries (Fin 2) ℂ_[p]) (flog W wq) +
        PowerSeries.subst (Xv 1 : MvPowerSeries (Fin 2) ℂ_[p]) (flog W wq)) :
    add (flog W wq) ex (Xv 0) (Xv 1) = F := by sorry
