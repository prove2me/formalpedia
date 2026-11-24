-- Prove2me | Theorems.Thm_PI_ZuckTensorWork_Cj_un_smul
-- name    : PI.ZuckTensorWork.Cj.un_smul
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T23:01:52.044087+00:00
-- url     : https://prove2.me/theorems/ab835f06-4cf2-4de2-b2df-69767f49a492
-- title:
--   Cj: un smul
-- statement:
--   The Cj construction uses the un smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ZuckermanTensor/DualDefs.lean#L34-L34
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ZuckermanTensor/DualDefs.lean#L34-L34

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

theorem PI.ZuckTensorWork.Cj.un_smul (c : ℂ) (x : Cj H) : un (c • x) = (starRingEnd ℂ) c • un x := by sorry
