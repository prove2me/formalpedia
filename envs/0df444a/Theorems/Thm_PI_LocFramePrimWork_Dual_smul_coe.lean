-- Prove2me | Theorems.Thm_PI_LocFramePrimWork_Dual_smul_coe
-- name    : PI.LocFramePrimWork.Dual_smul_coe
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:33:52.508981+00:00
-- url     : https://prove2.me/theorems/f06cd58a-643e-4c3c-bcb7-82aad9d85a6e
-- title:
--   Loc Frame Prim Work: Dual smul coe
-- statement:
--   The Loc Frame Prim Work construction uses the Dual smul coe property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalPrimitiveFrame/DualFunctionalsExist.lean#L16-L18
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalPrimitiveFrame/DualFunctionalsExist.lean#L16-L18

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

theorem PI.LocFramePrimWork.Dual_smul_coe (o : 𝓞 E) (y : Fin n → E) : o • y = (o : E) • y := by sorry
