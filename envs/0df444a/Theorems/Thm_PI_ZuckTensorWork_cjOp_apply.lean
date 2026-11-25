-- Prove2me | Theorems.Thm_PI_ZuckTensorWork_cjOp_apply
-- name    : PI.ZuckTensorWork.cjOp_apply
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T08:46:34.703485+00:00
-- url     : https://prove2.me/theorems/1429248d-2042-427c-8b68-b358b8447394
-- title:
--   Zuck Tensor Work: cj Op apply
-- statement:
--   The Zuck Tensor Work construction uses the cj Op apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ZuckermanTensor/DualDefs.lean#L67-L67
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ZuckermanTensor/DualDefs.lean#L67-L67

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UpqRep
import Definitions.Def_Formalism_PeriodIntegrals_IsLowUnitH
import Definitions.Def_Formalism_PeriodIntegrals_ZuckTensor
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ZuckermanTensor_DualDefs
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset
open scoped InnerProductSpace
noncomputable section
open PI PI.ZuckTensorWork
open PI.UpqRep PI.ZuckTensor
variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem PI.ZuckTensorWork.cjOp_apply (T : H →L[ℂ] H) (x : Cj H) : Cj.un (cjOp T x) = T (Cj.un x) := by sorry
