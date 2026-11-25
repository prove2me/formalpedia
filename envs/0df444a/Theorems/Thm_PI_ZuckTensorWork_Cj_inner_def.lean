-- Prove2me | Theorems.Thm_PI_ZuckTensorWork_Cj_inner_def
-- name    : PI.ZuckTensorWork.Cj.inner_def
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T08:46:17.994716+00:00
-- url     : https://prove2.me/theorems/93aff36d-6170-5ea4-88dc-f4c094dc3370
-- title:
--   Cj: inner def
-- statement:
--   The Cj construction uses the inner def property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ZuckermanTensor/DualDefs.lean#L50-L50
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ZuckermanTensor/DualDefs.lean#L50-L50

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
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem PI.ZuckTensorWork.Cj.inner_def (x y : Cj H) : ⟪x, y⟫_ℂ = ⟪un y, un x⟫_ℂ := by sorry
