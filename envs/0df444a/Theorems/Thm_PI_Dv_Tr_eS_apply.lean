-- Prove2me | Theorems.Thm_PI_Dv_Tr_eS_apply
-- name    : PI.Dv.Tr.eS_apply
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T05:28:30.455034+00:00
-- url     : https://prove2.me/theorems/21b05373-86b4-4aa8-bb10-9d45708ebd31
-- title:
--   Tr: e S apply
-- statement:
--   The Tr construction uses the e S apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/IdempotentTransfer/ESMulESOfNeZero.lean#L154-L161
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/IdempotentTransfer/ESMulESOfNeZero.lean#L154-L161

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

theorem PI.Dv.Tr.eS_apply (T : GoodSet K G) (s : T.S) (x : G) :
    (eS T s).coeff x = cf T s * LinearMap.trace K (T.W s) (T.tau s x⁻¹) := by sorry
