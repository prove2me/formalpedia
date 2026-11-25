-- Prove2me | Theorems.Thm_PI_ZuckTensorWork_cjSubInv_finiteDimensional
-- name    : PI.ZuckTensorWork.cjSubInv_finiteDimensional
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T08:46:59.672881+00:00
-- url     : https://prove2.me/theorems/41965846-a8ea-511a-9d2b-9164567be39d
-- title:
--   Zuck Tensor Work: cj Sub Inv finite Dimensional
-- statement:
--   The Zuck Tensor Work construction uses the cj Sub Inv finite Dimensional property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ZuckermanTensor/ConjRep.lean#L177-L183
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ZuckermanTensor/ConjRep.lean#L177-L183

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UpqRep
import Definitions.Def_Formalism_PeriodIntegrals_IsLowUnitH
import Definitions.Def_Formalism_PeriodIntegrals_ZuckTensor
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ZuckermanTensor_DualDefs
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ZuckermanTensor_DualChoice
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ZuckermanTensor_ConjRep
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
variable {n : ℕ}

theorem PI.ZuckTensorWork.cjSubInv_finiteDimensional (S : Submodule ℂ (Cj H)) [FiniteDimensional ℂ S] :
    FiniteDimensional ℂ (cjSubInv S) := by sorry
