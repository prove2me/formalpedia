-- Prove2me | Theorems.Thm_PI_ZuckTensorWork_revM_eq_submatrix
-- name    : PI.ZuckTensorWork.revM_eq_submatrix
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T23:15:27.874253+00:00
-- url     : https://prove2.me/theorems/22ab6110-2949-486d-913c-5165206a3207
-- title:
--   Zuck Tensor Work: rev M eq submatrix
-- statement:
--   The Zuck Tensor Work construction uses the rev M eq submatrix property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ZuckermanTensor/ConjRep.lean#L17-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ZuckermanTensor/ConjRep.lean#L17-L19

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

theorem PI.ZuckTensorWork.revM_eq_submatrix (g : Matrix (Fin n) (Fin n) ℂ) :
    revM g = g.submatrix (Fin.revPerm : Fin n ≃ Fin n) (Fin.revPerm : Fin n ≃ Fin n) := by sorry
