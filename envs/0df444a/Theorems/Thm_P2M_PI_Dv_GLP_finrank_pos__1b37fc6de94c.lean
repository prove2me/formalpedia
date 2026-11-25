-- Prove2me | Theorems.Thm_P2M_PI_Dv_GLP_finrank_pos__1b37fc6de94c
-- name    : P2M_PI_Dv_GLP_finrank_pos__1b37fc6de94c
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T04:56:04.418606+00:00
-- url     : https://prove2.me/theorems/df40c17d-524c-46d2-b917-8680fad8b0ad
-- title:
--   P2 M PI Dv GLP finrank pos  1b37fc6de94c: P2 M PI Dv GLP finrank pos  1b37fc6de94c
-- statement:
--   The P2 M PI Dv GLP finrank pos  1b37fc6de94c construction uses the P2 M PI Dv GLP finrank pos  1b37fc6de94c property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ProjectionLattices/FinrankIntertw.lean#L151-L152
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ProjectionLattices/FinrankIntertw.lean#L151-L152

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_SameFormAllLevels
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ProjectionLattices_FinrankIntertw
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.Dv PI.Dv.GLP
open Representation
variable {K : Type} [Field K] {G : Type} [Group G] [Fintype G]

theorem P2M_PI_Dv_GLP_finrank_pos__1b37fc6de94c (T : GoodSet K G) (s : T.S) : (0 : ℕ) < Module.finrank K (T.W s) := by sorry

alias «PI».«Dv».«GLP».«finrank_pos'» := P2M_PI_Dv_GLP_finrank_pos__1b37fc6de94c
