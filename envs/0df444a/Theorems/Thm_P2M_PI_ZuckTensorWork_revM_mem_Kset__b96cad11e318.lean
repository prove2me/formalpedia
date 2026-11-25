-- Prove2me | Theorems.Thm_P2M_PI_ZuckTensorWork_revM_mem_Kset__b96cad11e318
-- name    : P2M_PI_ZuckTensorWork_revM_mem_Kset__b96cad11e318
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T05:01:31.507969+00:00
-- url     : https://prove2.me/theorems/d4359e21-f00f-53ca-a94f-627cec142c37
-- title:
--   P2 M PI Zuck Tensor Work rev M mem Kset  b96cad11e318: P2 M PI Zuck Tensor Work rev M mem Kset  b96cad11e318
-- statement:
--   The P2 M PI Zuck Tensor Work rev M mem Kset  b96cad11e318 construction uses the P2 M PI Zuck Tensor Work rev M mem Kset  b96cad11e318 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ZuckermanTensor/ConjRep.lean#L81-L82
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ZuckermanTensor/ConjRep.lean#L81-L82

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

theorem P2M_PI_ZuckTensorWork_revM_mem_Kset__b96cad11e318 {ε : Fin n → Bool} {g : Matrix (Fin n) (Fin n) ℂ} (h : g ∈ Kset ε) :
    revM g ∈ Kset (revE ε) := by sorry

alias «PI».«ZuckTensorWork».«revM_mem_Kset'» := P2M_PI_ZuckTensorWork_revM_mem_Kset__b96cad11e318
