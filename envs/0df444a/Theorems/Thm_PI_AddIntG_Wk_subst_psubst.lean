-- Prove2me | Theorems.Thm_PI_AddIntG_Wk_subst_psubst
-- name    : PI.AddIntG.Wk.subst_psubst
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:50:18.374123+00:00
-- url     : https://prove2.me/theorems/c7504bc2-10c3-465e-9488-5972959c715e
-- title:
--   Wk: subst psubst
-- statement:
--   The Wk construction uses the subst psubst property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdditiveIntegralGroups/FormalGroupLawExists.lean#L29-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdditiveIntegralGroups/FormalGroupLawExists.lean#L29-L32

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdditiveIntegralGroups_VarZeroSubVarOneNe
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdditiveIntegralGroups_FormalGroupLawExists
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

theorem PI.AddIntG.Wk.subst_psubst {a : MvPowerSeries (Fin 2) ℂ_[p]} (ha : PowerSeries.HasSubst a)
    {b : Fin 2 → MvPowerSeries (Fin 2) ℂ_[p]} (hb : MvPowerSeries.HasSubst b) (f : PowerSeries ℂ_[p]) :
    MvPowerSeries.subst b (PowerSeries.subst a f) = PowerSeries.subst (MvPowerSeries.subst b a) f := by sorry
