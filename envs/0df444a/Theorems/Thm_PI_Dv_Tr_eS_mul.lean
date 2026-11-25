-- Prove2me | Theorems.Thm_PI_Dv_Tr_eS_mul
-- name    : PI.Dv.Tr.eS_mul
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T05:27:51.299702+00:00
-- url     : https://prove2.me/theorems/ccc036ca-0b94-4896-a2e8-c95b3a8a1e8c
-- title:
--   Tr: e S mul
-- statement:
--   The Tr construction uses the e S mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/IdempotentTransfer/ESMulESOfNeZero.lean#L57-L62
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/IdempotentTransfer/ESMulESOfNeZero.lean#L57-L62

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

theorem PI.Dv.Tr.eS_mul (T : GoodSet K G) (s : T.S) (a : MonoidAlgebra K G) :
    eS T s * a = phiS T s ((T.tau s).asAlgebraHom a) := by sorry
