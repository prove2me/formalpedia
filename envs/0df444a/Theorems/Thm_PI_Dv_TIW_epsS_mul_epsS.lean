-- Prove2me | Theorems.Thm_PI_Dv_TIW_epsS_mul_epsS
-- name    : PI.Dv.TIW.epsS_mul_epsS
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T08:18:49.934592+00:00
-- url     : https://prove2.me/theorems/b32ed4cc-4ae4-4110-99f0-cb0f7ea9c6b9
-- title:
--   TIW: eps S mul eps S
-- statement:
--   The TIW construction uses the eps S mul eps S property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/TransferIndices/MemOOfIsIntegral.lean#L135-L147
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/TransferIndices/MemOOfIsIntegral.lean#L135-L147

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
variable {K : Type} [Field K] [CharZero K] {G : Type} [Group G] [Fintype G]

theorem PI.Dv.TIW.epsS_mul_epsS (P : Pair K G) : epsS P * epsS P = ((Nat.card P.H : ℕ) : K) • epsS P := by sorry
