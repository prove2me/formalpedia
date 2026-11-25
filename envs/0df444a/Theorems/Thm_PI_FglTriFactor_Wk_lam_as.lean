-- Prove2me | Theorems.Thm_PI_FglTriFactor_Wk_lam_as
-- name    : PI.FglTriFactor.Wk.lam_as
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T05:30:46.250831+00:00
-- url     : https://prove2.me/theorems/c5cd4827-f1f0-4e17-b33c-44bea13c274d
-- title:
--   Wk: lam as
-- statement:
--   The Wk construction uses the lam as property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FormalGroupTriangles/SubstUpdateVarTwoLiftedThirdRoot.lean#L15-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FormalGroupTriangles/SubstUpdateVarTwoLiftedThirdRoot.lean#L15-L32

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

theorem PI.FglTriFactor.Wk.lam_as {W : WeierstrassCurve ℂ_[p]} {wq : PowerSeries ℂ_[p]} (h : IsWq W wq) :
    pr (MvPowerSeries.X 0 : MvPowerSeries (Fin 3) ℂ_[p]) (s3 W wq) (lam wq) = Lab wq := by sorry
