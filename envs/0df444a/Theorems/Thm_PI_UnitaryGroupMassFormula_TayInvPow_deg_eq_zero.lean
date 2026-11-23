-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_TayInvPow_deg_eq_zero
-- name    : PI.UnitaryGroupMassFormula.TayInvPow.deg_eq_zero
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:47:09.332773+00:00
-- url     : https://prove2.me/theorems/0220a4c5-d728-4086-a1f8-f631c559a081
-- title:
--   Tay Inv Pow: deg eq zero
-- statement:
--   The Tay Inv Pow construction uses the deg eq zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/TaylorInversePower/SumMultinomialSub.lean#L19-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/TaylorInversePower/SumMultinomialSub.lean#L19-L29

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

theorem PI.UnitaryGroupMassFormula.TayInvPow.deg_eq_zero {β : σ →₀ ℕ} : deg β = 0 ↔ β = 0 := by sorry
