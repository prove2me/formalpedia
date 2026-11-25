-- Prove2me | Theorems.Thm_PI_Dv_GLP_finrank_intertw
-- name    : PI.Dv.GLP.finrank_intertw
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T05:27:22.186716+00:00
-- url     : https://prove2.me/theorems/77696b67-45b7-5aba-b48f-d143927dfaeb
-- title:
--   GLP: finrank intertw
-- statement:
--   The GLP construction uses the finrank intertw property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ProjectionLattices/FinrankIntertw.lean#L81-L102
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ProjectionLattices/FinrankIntertw.lean#L81-L102

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

theorem PI.Dv.GLP.finrank_intertw (T : GoodSet K G) (s t : T.S) :
    Module.finrank K (IntertwiningMap (T.tau s) (T.tau t)) = if s = t then 1 else 0 := by sorry
