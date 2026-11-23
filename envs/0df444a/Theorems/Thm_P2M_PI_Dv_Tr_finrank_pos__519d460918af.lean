-- Prove2me | Theorems.Thm_P2M_PI_Dv_Tr_finrank_pos__519d460918af
-- name    : P2M_PI_Dv_Tr_finrank_pos__519d460918af
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:11:33.699694+00:00
-- url     : https://prove2.me/theorems/6158f3d7-0954-4430-9489-37ef08cafc22
-- title:
--   P2 M PI Dv Tr finrank pos  519d460918af: P2 M PI Dv Tr finrank pos  519d460918af
-- statement:
--   The P2 M PI Dv Tr finrank pos  519d460918af construction uses the P2 M PI Dv Tr finrank pos  519d460918af property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/IdempotentTransfer/ESMulESOfNeZero.lean#L91-L91
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/IdempotentTransfer/ESMulESOfNeZero.lean#L91-L91

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

theorem P2M_PI_Dv_Tr_finrank_pos__519d460918af (T : GoodSet K G) (s : T.S) : 0 < Module.finrank K (T.W s) := by sorry

alias «PI».«Dv».«Tr».«finrank_pos'» := P2M_PI_Dv_Tr_finrank_pos__519d460918af
