-- Prove2me | Theorems.Thm_PI_LocFramePrimWork_Dual_ne_zero
-- name    : PI.LocFramePrimWork.Dual_ne_zero
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T08:12:59.780042+00:00
-- url     : https://prove2.me/theorems/650e9634-649a-5221-ae33-e57d1cc462c7
-- title:
--   Loc Frame Prim Work: Dual ne zero
-- statement:
--   The Loc Frame Prim Work construction uses the Dual ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalPrimitiveFrame/DualFunctionalsExist.lean#L20-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalPrimitiveFrame/DualFunctionalsExist.lean#L20-L32

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalPrimitiveFrame_StepsTop
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalPrimitiveFrame_DualFunctionalsExist
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.LocFramePrimWork
open NumberField IsDedekindDomain PI.LocFramePrim Module
open scoped TensorProduct
variable {E : Type} [Field E] [NumberField E] {n : ℕ}

theorem PI.LocFramePrimWork.Dual_ne_zero (Lb : Submodule (𝓞 E) (Fin n → E)) (z : Fin n → E)
    (hprim : ∀ c : E, c • z ∈ Lb → ∃ o : 𝓞 E, (o : E) = c) : z ≠ 0 := by sorry
