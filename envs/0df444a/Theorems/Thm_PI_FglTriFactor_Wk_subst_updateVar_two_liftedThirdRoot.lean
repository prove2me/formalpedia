-- Prove2me | Theorems.Thm_PI_FglTriFactor_Wk_subst_updateVar_two_liftedThirdRoot
-- name    : PI.FglTriFactor.Wk.subst_updateVar_two_liftedThirdRoot
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:26:23.124087+00:00
-- url     : https://prove2.me/theorems/1b36f54d-bd78-440c-ad60-8e8b2a42544c
-- title:
--   Wk: subst update Var two lifted Third Root
-- statement:
--   The Wk construction uses the subst update Var two lifted Third Root property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FormalGroupTriangles/SubstUpdateVarTwoLiftedThirdRoot.lean#L46-L73
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FormalGroupTriangles/SubstUpdateVarTwoLiftedThirdRoot.lean#L46-L73

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

theorem PI.FglTriFactor.Wk.subst_updateVar_two_liftedThirdRoot (W : WeierstrassCurve ℂ_[p]) (wq : PowerSeries ℂ_[p]) (t : MvPowerSeries (Fin 3) ℂ_[p])
    (ht : MvPowerSeries.constantCoeff t = 0) : MvPowerSeries.subst (upd 2 t) (s3 W wq) = s3 W wq := by sorry
