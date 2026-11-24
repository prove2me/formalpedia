-- Prove2me | Theorems.Thm_P2M_PI_ZuckTensorWork_revM_mem_UJset__7a93c3174ea3
-- name    : P2M_PI_ZuckTensorWork_revM_mem_UJset__7a93c3174ea3
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T23:17:03.899909+00:00
-- url     : https://prove2.me/theorems/28a3dfbb-5e70-4d36-b436-72674d8a98ef
-- title:
--   P2 M PI Zuck Tensor Work rev M mem UJset  7a93c3174ea3: P2 M PI Zuck Tensor Work rev M mem UJset  7a93c3174ea3
-- statement:
--   The P2 M PI Zuck Tensor Work rev M mem UJset  7a93c3174ea3 construction uses the P2 M PI Zuck Tensor Work rev M mem UJset  7a93c3174ea3 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ZuckermanTensor/ConjRep.lean#L67-L68
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ZuckermanTensor/ConjRep.lean#L67-L68

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

theorem P2M_PI_ZuckTensorWork_revM_mem_UJset__7a93c3174ea3 {ε : Fin n → Bool} {g : Matrix (Fin n) (Fin n) ℂ} (h : g ∈ UJset ε) :
    revM g ∈ UJset (revE ε) := by sorry

alias «PI».«ZuckTensorWork».«revM_mem_UJset'» := P2M_PI_ZuckTensorWork_revM_mem_UJset__7a93c3174ea3
