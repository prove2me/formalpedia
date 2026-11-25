-- Prove2me | Theorems.Thm_PI_Dv_TIW_coeff_sum_of
-- name    : PI.Dv.TIW.coeff_sum_of
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T05:28:49.510682+00:00
-- url     : https://prove2.me/theorems/368d1a53-bc54-4f7c-8329-a748c6d9000f
-- title:
--   TIW: coeff sum of
-- statement:
--   The TIW construction uses the coeff sum of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/TransferIndices/MemOOfIsIntegral.lean#L16-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/TransferIndices/MemOOfIsIntegral.lean#L16-L20

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

theorem PI.Dv.TIW.coeff_sum_of (a : G → K) (g : G) :
    (∑ y : G, a y • MonoidAlgebra.of K G y).coeff g = a g := by sorry
