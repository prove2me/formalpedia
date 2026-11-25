-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_TayInvPow_cprod_add
-- name    : PI.UnitaryGroupMassFormula.TayInvPow.cprod_add
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T05:40:09.93966+00:00
-- url     : https://prove2.me/theorems/8c90f5f4-7862-4cd3-85f7-78ee94f2e675
-- title:
--   Tay Inv Pow: cprod add
-- statement:
--   The Tay Inv Pow construction uses the cprod add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/TaylorInversePower/SumMultinomialSub.lean#L33-L34
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/TaylorInversePower/SumMultinomialSub.lean#L33-L34

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

theorem PI.UnitaryGroupMassFormula.TayInvPow.cprod_add (c : σ →₀ A) (β γ : σ →₀ ℕ) : cprod c (β + γ) = cprod c β * cprod c γ := by sorry
