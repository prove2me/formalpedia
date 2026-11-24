-- Prove2me | Theorems.Thm_PI_ZuckTensorWork_Cj_un_mk
-- name    : PI.ZuckTensorWork.Cj.un_mk
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T23:01:46.363189+00:00
-- url     : https://prove2.me/theorems/b2b3a7fe-4004-473e-8a7e-9ff3bbaa5406
-- title:
--   Cj: un mk
-- statement:
--   The Cj construction uses the un mk property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ZuckermanTensor/DualDefs.lean#L21-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ZuckermanTensor/DualDefs.lean#L21-L21

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
open PI.ZuckTensorWork.Cj
variable {H : Type}

theorem PI.ZuckTensorWork.Cj.un_mk (x : H) : un (mk x) = x := by sorry

attribute [defeq] PI.ZuckTensorWork.Cj.un_mk
