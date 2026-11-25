-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_TayInvPow_cprod_single
-- name    : PI.UnitaryGroupMassFormula.TayInvPow.cprod_single
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T05:39:57.223203+00:00
-- url     : https://prove2.me/theorems/0c4902be-7641-5387-ac39-632d25391985
-- title:
--   Tay Inv Pow: cprod single
-- statement:
--   The Tay Inv Pow construction uses the cprod single property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/TaylorInversePower/SumMultinomialSub.lean#L36-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/TaylorInversePower/SumMultinomialSub.lean#L36-L37

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

theorem PI.UnitaryGroupMassFormula.TayInvPow.cprod_single (c : σ →₀ A) (p : σ) (n : ℕ) : cprod c (Finsupp.single p n) = c p ^ n := by sorry
