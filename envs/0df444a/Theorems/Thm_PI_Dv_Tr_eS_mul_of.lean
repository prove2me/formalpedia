-- Prove2me | Theorems.Thm_PI_Dv_Tr_eS_mul_of
-- name    : PI.Dv.Tr.eS_mul_of
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T05:29:06.405241+00:00
-- url     : https://prove2.me/theorems/4c5c3805-e35f-5b97-b620-be9c5633e794
-- title:
--   Tr: e S mul of
-- statement:
--   The Tr construction uses the e S mul of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/IdempotentTransfer/ESMulESOfNeZero.lean#L39-L48
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/IdempotentTransfer/ESMulESOfNeZero.lean#L39-L48

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_SameFormAllLevels
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IdempotentTransfer_ESMulESOfNeZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.Dv PI.Dv.Tr
open PI.Dv
variable {K : Type} [Field K] [CharZero K] {G : Type} [Group G] [Fintype G]

theorem PI.Dv.Tr.eS_mul_of (T : GoodSet K G) (s : T.S) (y : G) :
    eS T s * MonoidAlgebra.of K G y = phiS T s (T.tau s y) := by sorry
