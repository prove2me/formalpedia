-- Prove2me | Theorems.Thm_PI_FglPhSplit_Wk_subst_zero_of
-- name    : PI.FglPhSplit.Wk.subst_zero_of
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T05:30:10.761804+00:00
-- url     : https://prove2.me/theorems/32f9a836-3862-4157-99d3-9909b12c7224
-- title:
--   Wk: subst zero of
-- statement:
--   The Wk construction uses the subst zero of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FormalGroupSplitting/OrthogonalSplitPolarizationVanishes.lean#L54-L57
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FormalGroupSplitting/OrthogonalSplitPolarizationVanishes.lean#L54-L57

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FormalGroupSplitting_Development
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FormalGroupSplitting_OrthogonalSplitPolarizationVanishes
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.FglPhSplit PI.FglPhSplit.Wk
open PI.FglPhSplit
variable {K : Type} [Field K]

theorem PI.FglPhSplit.Wk.subst_zero_of {τ : Type} (f : PowerSeries K) (hf : PowerSeries.constantCoeff f = 0) :
    PowerSeries.subst (0 : MvPowerSeries τ K) f = 0 := by sorry
