-- Prove2me | Theorems.Thm_PI_FglTriFactor_Wk_zc_mu
-- name    : PI.FglTriFactor.Wk.zc_mu
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T05:30:05.370975+00:00
-- url     : https://prove2.me/theorems/3cc19693-035c-5597-afc8-6bac8a5d0bb2
-- title:
--   Wk: zc mu
-- statement:
--   The Wk construction uses the zc mu property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FormalGroupTriangles/SubstUpdateVarTwoLiftedThirdRoot.lean#L125-L141
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FormalGroupTriangles/SubstUpdateVarTwoLiftedThirdRoot.lean#L125-L141

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FormalGroupTriangles_LiftedThirdRootSubXZeroNeZero
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FormalGroupTriangles_SubstUpdateVarTwoLiftedThirdRoot
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
open PI.AddIntG.Wk (SerS mem_SerS mvsubst_mem_SerS lam nu wser wv Z3)
variable {p : ℕ} [Fact p.Prime]

theorem PI.FglTriFactor.Wk.zc_mu {wq : PowerSeries ℂ_[p]} {μ : MvPowerSeries (Fin 3) ℂ_[p]}
    (hμ : Lac wq - Lab wq = (MvPowerSeries.X 2 - MvPowerSeries.X 1) * μ) :
    MvPowerSeries.subst (zc (p := p)) μ = MvPowerSeries.X 2 * PowerSeries.subst (MvPowerSeries.X 2 : MvPowerSeries (Fin 3) ℂ_[p]) wq := by sorry
