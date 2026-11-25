-- Prove2me | Theorems.Thm_PI_Dv_Tr_eS_mul_eS_of_ne_zero
-- name    : PI.Dv.Tr.eS_mul_eS_of_ne_zero
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T05:29:07.054557+00:00
-- url     : https://prove2.me/theorems/a8d8f05e-b320-5c43-91bd-2a9181fd0f54
-- title:
--   Tr: e S mul e S of ne zero
-- statement:
--   The Tr construction uses the e S mul e S of ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/IdempotentTransfer/ESMulESOfNeZero.lean#L138-L152
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/IdempotentTransfer/ESMulESOfNeZero.lean#L138-L152

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

theorem PI.Dv.Tr.eS_mul_eS_of_ne_zero (T : GoodSet K G) (s t : T.S) (h : eS T s * eS T t ≠ 0) :
    eS T s * eS T t = eS T t := by sorry
