-- Prove2me | Theorems.Thm_PI_ZuckTensorWork_Cj_mk_un
-- name    : PI.ZuckTensorWork.Cj.mk_un
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T23:01:24.601594+00:00
-- url     : https://prove2.me/theorems/d70331d0-0392-45da-b923-8976443d08ee
-- title:
--   Cj: mk un
-- statement:
--   The Cj construction uses the mk un property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ZuckermanTensor/DualDefs.lean#L22-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ZuckermanTensor/DualDefs.lean#L22-L22

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

theorem PI.ZuckTensorWork.Cj.mk_un (x : Cj H) : mk (un x) = x := by sorry

attribute [defeq] PI.ZuckTensorWork.Cj.mk_un
