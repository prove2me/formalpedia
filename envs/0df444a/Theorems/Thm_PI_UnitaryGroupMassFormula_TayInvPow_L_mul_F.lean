-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_TayInvPow_L_mul_F
-- name    : PI.UnitaryGroupMassFormula.TayInvPow.L_mul_F
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T05:39:57.382826+00:00
-- url     : https://prove2.me/theorems/8797f6dc-4965-4aef-9782-aac4c36d5411
-- title:
--   Tay Inv Pow: L mul F
-- statement:
--   The Tay Inv Pow construction uses the L mul F property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/TaylorInversePower/SumMultinomialSub.lean#L133-L165
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/TaylorInversePower/SumMultinomialSub.lean#L133-L165

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

theorem PI.UnitaryGroupMassFormula.TayInvPow.L_mul_F (c : σ →₀ A) (s t : A) (hst : s * t = 1) (k : ℕ) :
    (C s + c.sum (fun p a => C a * X p)) * F c t (k + 1) = F c t k := by sorry
