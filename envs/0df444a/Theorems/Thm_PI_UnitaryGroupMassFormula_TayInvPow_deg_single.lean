-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_TayInvPow_deg_single
-- name    : PI.UnitaryGroupMassFormula.TayInvPow.deg_single
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T05:40:27.528269+00:00
-- url     : https://prove2.me/theorems/68927d8d-a749-49ee-978c-51debf9eb974
-- title:
--   Tay Inv Pow: deg single
-- statement:
--   The Tay Inv Pow construction uses the deg single property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/TaylorInversePower/SumMultinomialSub.lean#L16-L17
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/TaylorInversePower/SumMultinomialSub.lean#L16-L17

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

theorem PI.UnitaryGroupMassFormula.TayInvPow.deg_single (p : σ) (n : ℕ) : deg (Finsupp.single p n) = n := by sorry
