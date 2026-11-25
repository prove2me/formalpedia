-- Prove2me | Theorems.Thm_PI_AddIntG_Wk_lam_mem
-- name    : PI.AddIntG.Wk.lam_mem
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T05:22:57.098642+00:00
-- url     : https://prove2.me/theorems/53048589-3818-557c-98bb-b079b3d9a43d
-- title:
--   Wk: lam mem
-- statement:
--   The Wk construction uses the lam mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdditiveIntegralGroups/CoeffWSeriesVarZero.lean#L82-L86
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdditiveIntegralGroups/CoeffWSeriesVarZero.lean#L82-L86

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

theorem PI.AddIntG.Wk.lam_mem {S : Subring ℂ_[p]} {wq : PowerSeries ℂ_[p]} (hS : ∀ n, PowerSeries.coeff n wq ∈ S) :
    ∀ e, MvPowerSeries.coeff e (lam wq) ∈ S := by sorry
