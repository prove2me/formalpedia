-- Prove2me | Theorems.Thm_PI_FglPhSplit_Wk_allIn_subst_X
-- name    : PI.FglPhSplit.Wk.allIn_subst_X
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:26:11.092184+00:00
-- url     : https://prove2.me/theorems/7841f9a7-2e5a-4245-9d63-269d21d1fcd6
-- title:
--   Wk: all In subst X
-- statement:
--   The Wk construction uses the all In subst X property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FormalGroupSplitting/ExpCongruenceExtendsToSum.lean#L44-L57
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FormalGroupSplitting/ExpCongruenceExtendsToSum.lean#L44-L57

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FormalGroupSplitting_AddPreservesExpCongruence
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FormalGroupSplitting_OrthogonalSplitPolarizationVanishes
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FormalGroupSplitting_ExpCongruenceExtendsToSum
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

theorem PI.FglPhSplit.Wk.allIn_subst_X {W : Subring K} {σ τ : Type} (r : σ → τ)
    (ha : MvPowerSeries.HasSubst (fun s => (MvPowerSeries.X (r s) : MvPowerSeries τ K)))
    {H : MvPowerSeries σ K} (hH : AllIn W H) :
    AllIn W (MvPowerSeries.subst (fun s => (MvPowerSeries.X (r s) : MvPowerSeries τ K)) H) := by sorry
