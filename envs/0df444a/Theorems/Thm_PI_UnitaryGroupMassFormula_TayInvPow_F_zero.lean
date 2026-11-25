-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_TayInvPow_F_zero
-- name    : PI.UnitaryGroupMassFormula.TayInvPow.F_zero
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T05:40:09.128737+00:00
-- url     : https://prove2.me/theorems/51dce78c-10d6-4999-acc8-235e257748ec
-- title:
--   Tay Inv Pow: F zero
-- statement:
--   The Tay Inv Pow construction uses the F zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/TaylorInversePower/SumMultinomialSub.lean#L123-L131
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/TaylorInversePower/SumMultinomialSub.lean#L123-L131

import Definitions.Def_Formalism_PeriodIntegrals_TayInvPow
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TaylorInversePower_SumMultinomialSub
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.TayInvPow
open MvPowerSeries
variable {σ : Type*} {A : Type*} [CommRing A]

theorem PI.UnitaryGroupMassFormula.TayInvPow.F_zero (c : σ →₀ A) (t : A) : F c t 0 = 1 := by sorry
