-- Prove2me | Theorems.Thm_PI_Dv_TIW_eS_mul_eS
-- name    : PI.Dv.TIW.eS_mul_eS
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T05:28:35.969902+00:00
-- url     : https://prove2.me/theorems/5ae9048f-f674-4bfc-9ea4-9dcfa56711d2
-- title:
--   TIW: e S mul e S
-- statement:
--   The TIW construction uses the e S mul e S property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/TransferIndices/MemOOfIsIntegral.lean#L80-L83
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/TransferIndices/MemOOfIsIntegral.lean#L80-L83

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TransferIndices_TauCentralScalar
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TransferIndices_GrpNorm
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TransferIndices_DvTransferIdxOf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TransferIndices_MemOOfIsIntegral
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.Dv PI.Dv.TIW
open PI.Dv NumberField
variable {K : Type} [Field K] [CharZero K] {G : Type} [Group G] [Fintype G] (T : GoodSet K G)

theorem PI.Dv.TIW.eS_mul_eS (s t : T.S) : eS T s * eS T t = if s = t then eS T s else 0 := by sorry
