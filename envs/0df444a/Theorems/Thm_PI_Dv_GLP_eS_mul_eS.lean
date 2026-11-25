-- Prove2me | Theorems.Thm_PI_Dv_GLP_eS_mul_eS
-- name    : PI.Dv.GLP.eS_mul_eS
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T05:27:16.652924+00:00
-- url     : https://prove2.me/theorems/132340b0-fd28-5de4-87d7-edbcbd663e6b
-- title:
--   GLP: e S mul e S
-- statement:
--   The GLP construction uses the e S mul e S property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ProjectionLattices/FinrankIntertw.lean#L197-L211
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ProjectionLattices/FinrankIntertw.lean#L197-L211

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

theorem PI.Dv.GLP.eS_mul_eS [CharZero K] (T : GoodSet K G) (s t : T.S) :
    eS T s * eS T t = if s = t then eS T s else 0 := by sorry
