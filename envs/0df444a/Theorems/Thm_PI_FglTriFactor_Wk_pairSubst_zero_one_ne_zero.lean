-- Prove2me | Theorems.Thm_PI_FglTriFactor_Wk_pairSubst_zero_one_ne_zero
-- name    : PI.FglTriFactor.Wk.pairSubst_zero_one_ne_zero
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:26:40.583804+00:00
-- url     : https://prove2.me/theorems/798d4f9f-eba3-4c03-ae69-6b70842c873a
-- title:
--   Wk: pair Subst zero one ne zero
-- statement:
--   The Wk construction uses the pair Subst zero one ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FormalGroupTriangles/LiftedThirdRootSubXZeroNeZero.lean#L187-L194
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FormalGroupTriangles/LiftedThirdRootSubXZeroNeZero.lean#L187-L194

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FormalGroupTriangles_PairSubstXZero
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdditiveIntegralGroups_FormalGroupLawExists
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FormalGroupTriangles_LiftedThirdRootSubXZeroNeZero
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

theorem PI.FglTriFactor.Wk.pairSubst_zero_one_ne_zero {g : MvPowerSeries (Fin 2) ℂ_[p]} (hg : g ≠ 0) :
    pr (MvPowerSeries.X 0 : MvPowerSeries (Fin 3) ℂ_[p]) (MvPowerSeries.X 1) g ≠ 0 := by sorry
