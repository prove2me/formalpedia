-- Prove2me | Theorems.Thm_PI_FglPhSplit_Wk_pt_lg
-- name    : PI.FglPhSplit.Wk.pt_lg
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:48:03.54743+00:00
-- url     : https://prove2.me/theorems/eba116b7-16ed-45c2-b1d4-e385cadd2fe8
-- title:
--   Wk: pt lg
-- statement:
--   The Wk construction uses the pt lg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FormalGroupSplitting/OrthogonalSplitPolarizationVanishes.lean#L59-L65
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FormalGroupSplitting/OrthogonalSplitPolarizationVanishes.lean#L59-L65

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

theorem PI.FglPhSplit.Wk.pt_lg (g : Dat K) {τ : Type} (hl0 : PowerSeries.constantCoeff g.l = 0)
    (hinv : PowerSeries.subst g.l g.ex = PowerSeries.X) {y : MvPowerSeries τ K}
    (hy : MvPowerSeries.constantCoeff y = 0) : g.pt (g.lg y) = y := by sorry
