-- Prove2me | Theorems.Thm_PI_FglTriFactor_Wk_eq_of_X_two_mul_eq
-- name    : PI.FglTriFactor.Wk.eq_of_X_two_mul_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T03:00:44.282333+00:00
-- url     : https://prove2.me/theorems/55dc58e4-dd2e-4832-b598-14286d10fc53
-- title:
--   Wk: eq of X two mul eq
-- statement:
--   The Wk construction uses the eq of X two mul eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FormalGroupTriangles/SubstUpdateVarTwoLiftedThirdRoot.lean#L118-L123
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FormalGroupTriangles/SubstUpdateVarTwoLiftedThirdRoot.lean#L118-L123

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

theorem PI.FglTriFactor.Wk.eq_of_X_two_mul_eq {f g : MvPowerSeries (Fin 3) ℂ_[p]} (h : MvPowerSeries.X 2 * f = MvPowerSeries.X 2 * g) :
    f = g := by sorry
