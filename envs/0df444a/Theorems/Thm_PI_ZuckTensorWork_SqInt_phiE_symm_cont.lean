-- Prove2me | Theorems.Thm_PI_ZuckTensorWork_SqInt_phiE_symm_cont
-- name    : PI.ZuckTensorWork.SqInt.phiE_symm_cont
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T08:46:29.906812+00:00
-- url     : https://prove2.me/theorems/4d5d5e44-21e2-5558-8dbc-3aeeb2f1acbd
-- title:
--   Sq Int: phi E symm cont
-- statement:
--   The Sq Int construction uses the phi E symm cont property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ZuckermanTensor/SquareIntegrableConj.lean#L77-L80
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ZuckermanTensor/SquareIntegrableConj.lean#L77-L80

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UpqRep
import Definitions.Def_Formalism_PeriodIntegrals_IsLowUnitH
import Definitions.Def_Formalism_PeriodIntegrals_ZuckTensor
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ZuckermanTensor_DualDefs
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ZuckermanTensor_DualChoice
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ZuckermanTensor_SquareIntegrableConj
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Matrix Finset
open scoped InnerProductSpace NNReal ENNReal
noncomputable section
open PI PI.ZuckTensorWork
open PI.UpqRep PI.ZuckTensor
open PI.ZuckTensorWork.SqInt
variable {n : ℕ}

theorem PI.ZuckTensorWork.SqInt.phiE_symm_cont (ε : Fin n → Bool) : Continuous (phiE ε).symm := by sorry
