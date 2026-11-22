-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_TayInvPow_coeff_F
-- name    : PI.UnitaryGroupMassFormula.TayInvPow.coeff_F
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T23:17:23.178216+00:00
-- url     : https://prove2.me/theorems/0480a01e-b730-4068-8c91-baca6970eb9c
-- title:
--   Tay Inv Pow: coeff F
-- statement:
--   The Tay Inv Pow construction uses the coeff F property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/TaylorInversePower/SumMultinomialSub.lean#L121-L121
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/TaylorInversePower/SumMultinomialSub.lean#L121-L121

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

theorem PI.UnitaryGroupMassFormula.TayInvPow.coeff_F (c : σ →₀ A) (t : A) (k : ℕ) (β : σ →₀ ℕ) : coeff β (F c t k) = cf c t k β := by sorry
