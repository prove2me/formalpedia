-- Prove2me | Theorems.Thm_PI_FglPhSplit_Wk_be_mulBy_zero
-- name    : PI.FglPhSplit.Wk.be_mulBy_zero
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T02:43:21.353634+00:00
-- url     : https://prove2.me/theorems/6841c1e1-c3c2-4e89-bf6b-6e472414d9c9
-- title:
--   Wk: be mul By zero
-- statement:
--   The Wk construction uses the be mul By zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FormalGroupSplitting/OrthogonalSplitPolarizationVanishes.lean#L67-L80
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FormalGroupSplitting/OrthogonalSplitPolarizationVanishes.lean#L67-L80

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

theorem PI.FglPhSplit.Wk.be_mulBy_zero (g : Dat K) {τ : Type} (hex0 : PowerSeries.constantCoeff g.ex = 0)
    (hph0 : PowerSeries.constantCoeff g.ph = 0) (hl0 : PowerSeries.constantCoeff g.l = 0)
    (hinv : PowerSeries.subst g.l g.ex = PowerSeries.X) (x : MvPowerSeries τ K)
    {y : MvPowerSeries τ K} (hy : MvPowerSeries.constantCoeff y = 0) :
    g.be (g.mulBy 0 x) y = 0 := by sorry
