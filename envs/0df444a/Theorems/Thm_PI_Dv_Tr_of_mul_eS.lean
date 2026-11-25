-- Prove2me | Theorems.Thm_PI_Dv_Tr_of_mul_eS
-- name    : PI.Dv.Tr.of_mul_eS
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T05:28:29.521583+00:00
-- url     : https://prove2.me/theorems/16dddd0e-d24d-5333-81ff-46417d069a42
-- title:
--   Tr: of mul e S
-- statement:
--   The Tr construction uses the of mul e S property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/IdempotentTransfer/ESMulESOfNeZero.lean#L31-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/IdempotentTransfer/ESMulESOfNeZero.lean#L31-L37

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

theorem PI.Dv.Tr.of_mul_eS (T : GoodSet K G) (s : T.S) (y : G) :
    MonoidAlgebra.of K G y * eS T s = phiS T s (T.tau s y) := by sorry
