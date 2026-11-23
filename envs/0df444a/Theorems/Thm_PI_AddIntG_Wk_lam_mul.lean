-- Prove2me | Theorems.Thm_PI_AddIntG_Wk_lam_mul
-- name    : PI.AddIntG.Wk.lam_mul
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T02:50:30.365551+00:00
-- url     : https://prove2.me/theorems/d370eef8-994d-4de3-b93e-6b04f7fc2277
-- title:
--   Wk: lam mul
-- statement:
--   The Wk construction uses the lam mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdditiveIntegralGroups/CoeffWSeriesVarZero.lean#L45-L65
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdditiveIntegralGroups/CoeffWSeriesVarZero.lean#L45-L65

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdditiveIntegralGroups_CoeffPowMemS
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdditiveIntegralGroups_CoeffWSeriesVarZero
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

theorem PI.AddIntG.Wk.lam_mul (wq : PowerSeries ℂ_[p]) :
    (Xv 1 - Xv 0 : MvPowerSeries (Fin 2) ℂ_[p]) * lam wq = wv wq 1 - wv wq 0 := by sorry
