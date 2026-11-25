-- Prove2me | Theorems.Thm_PI_AddIntG_Wk_omega_at
-- name    : PI.AddIntG.Wk.omega_at
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T05:22:19.898801+00:00
-- url     : https://prove2.me/theorems/bdc20b56-0437-5542-95ad-924bdb5b09fc
-- title:
--   Wk: omega at
-- statement:
--   The Wk construction uses the omega at property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdditiveIntegralGroups/VarZeroSubVarOneNe.lean#L18-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdditiveIntegralGroups/VarZeroSubVarOneNe.lean#L18-L25

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

theorem PI.AddIntG.Wk.omega_at {W : WeierstrassCurve ℂ_[p]} {wq : PowerSeries ℂ_[p]} (h : IsWq W wq)
    {r : MvPowerSeries (Fin 2) ℂ_[p]} (hr : MvPowerSeries.constantCoeff r = 0) :
    PowerSeries.subst r (omegaW W wq) * Gv W r (PowerSeries.subst r (wser wq)) = -1 := by sorry
