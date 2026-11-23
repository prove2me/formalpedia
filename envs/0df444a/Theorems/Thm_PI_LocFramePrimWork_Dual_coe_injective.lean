-- Prove2me | Theorems.Thm_PI_LocFramePrimWork_Dual_coe_injective
-- name    : PI.LocFramePrimWork.Dual_coe_injective
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:33:26.460899+00:00
-- url     : https://prove2.me/theorems/2342fb6f-7ac5-424a-867a-aa72e8c3021c
-- title:
--   Loc Frame Prim Work: Dual coe injective
-- statement:
--   The Loc Frame Prim Work construction uses the Dual coe injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalPrimitiveFrame/DualFunctionalsExist.lean#L14-L14
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalPrimitiveFrame/DualFunctionalsExist.lean#L14-L14

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

theorem PI.LocFramePrimWork.Dual_coe_injective : Function.Injective ((↑) : 𝓞 E → E) := by sorry
