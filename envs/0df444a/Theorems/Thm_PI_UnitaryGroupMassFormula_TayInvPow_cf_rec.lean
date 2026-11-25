-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_TayInvPow_cf_rec
-- name    : PI.UnitaryGroupMassFormula.TayInvPow.cf_rec
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T05:40:15.958897+00:00
-- url     : https://prove2.me/theorems/2dac8543-cac6-4ae0-83ac-72d905f555b9
-- title:
--   Tay Inv Pow: cf rec
-- statement:
--   The Tay Inv Pow construction uses the cf rec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/TaylorInversePower/SumMultinomialSub.lean#L79-L117
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/TaylorInversePower/SumMultinomialSub.lean#L79-L117

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

theorem PI.UnitaryGroupMassFormula.TayInvPow.cf_rec (c : σ →₀ A) (s t : A) (hst : s * t = 1) (k : ℕ) (β : σ →₀ ℕ) :
    s * cf c t (k + 1) β + ∑ p ∈ β.support, c p * cf c t (k + 1) (β - Finsupp.single p 1 : σ →₀ ℕ) =
      cf c t k β := by sorry
