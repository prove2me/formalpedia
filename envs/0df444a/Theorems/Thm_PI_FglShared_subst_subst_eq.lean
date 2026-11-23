-- Prove2me | Theorems.Thm_PI_FglShared_subst_subst_eq
-- name    : PI.FglShared.subst_subst_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:26:03.975788+00:00
-- url     : https://prove2.me/theorems/e36a7e67-fe78-44f2-9616-422a55088312
-- title:
--   Fgl Shared: subst subst eq
-- statement:
--   The Fgl Shared construction uses the subst subst eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FormalGroupCommon/CoeffSingleLg.lean#L18-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FormalGroupCommon/CoeffSingleLg.lean#L18-L23

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FormalGroupCommon_ExpLog
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FormalGroupCommon_CoeffSingleLg
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.FglShared
open MvPowerSeries
variable {p : ℕ} [Fact p.Prime]

theorem PI.FglShared.subst_subst_eq {σ : Type} {l ex : PowerSeries ℂ_[p]} (hex0 : PowerSeries.constantCoeff ex = 0)
    (hinv : PowerSeries.subst ex l = PowerSeries.X) {y : MvPowerSeries σ ℂ_[p]}
    (hy : constantCoeff y = 0) : PowerSeries.subst (PowerSeries.subst y ex) l = y := by sorry
