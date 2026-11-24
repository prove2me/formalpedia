-- Prove2me | Theorems.Thm_PI_ZuckTensorWork_Cj_mk_smul
-- name    : PI.ZuckTensorWork.Cj.mk_smul
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T23:15:30.914898+00:00
-- url     : https://prove2.me/theorems/822d009c-7fb2-4d06-a325-a0db7d8b681c
-- title:
--   Cj: mk smul
-- statement:
--   The Cj construction uses the mk smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ZuckermanTensor/ConjRep.lean#L89-L91
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ZuckermanTensor/ConjRep.lean#L89-L91

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

theorem PI.ZuckTensorWork.Cj.mk_smul (c : ℂ) (x : H) : Cj.mk (c • x) = (starRingEnd ℂ) c • Cj.mk x := by sorry
