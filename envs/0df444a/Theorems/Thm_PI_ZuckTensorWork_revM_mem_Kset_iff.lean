-- Prove2me | Theorems.Thm_PI_ZuckTensorWork_revM_mem_Kset_iff
-- name    : PI.ZuckTensorWork.revM_mem_Kset_iff
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T23:15:44.872452+00:00
-- url     : https://prove2.me/theorems/9506809d-58bd-47d2-aa74-8e42ad7b75dc
-- title:
--   Zuck Tensor Work: rev M mem Kset iff
-- statement:
--   The Zuck Tensor Work construction uses the rev M mem Kset iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ZuckermanTensor/ConjRep.lean#L70-L76
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ZuckermanTensor/ConjRep.lean#L70-L76

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
variable {n : ℕ}

theorem PI.ZuckTensorWork.revM_mem_Kset_iff {ε : Fin n → Bool} {g : Matrix (Fin n) (Fin n) ℂ} :
    revM g ∈ Kset ε ↔ g ∈ Kset (revE ε) := by sorry
