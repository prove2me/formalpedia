-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_TayInvPow_sum_multinomial_sub
-- name    : PI.UnitaryGroupMassFormula.TayInvPow.sum_multinomial_sub
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T05:40:17.426521+00:00
-- url     : https://prove2.me/theorems/f2353f18-0c9e-4eb2-aefc-8439988ea0a0
-- title:
--   Tay Inv Pow: sum multinomial sub
-- statement:
--   The Tay Inv Pow construction uses the sum multinomial sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/TaylorInversePower/SumMultinomialSub.lean#L39-L73
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/TaylorInversePower/SumMultinomialSub.lean#L39-L73

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

theorem PI.UnitaryGroupMassFormula.TayInvPow.sum_multinomial_sub (β : σ →₀ ℕ) (hβ : β ≠ 0) :
    ∑ p ∈ β.support, Nat.multinomial β.support (β - Finsupp.single p 1 : σ →₀ ℕ) =
      Nat.multinomial β.support β := by sorry
