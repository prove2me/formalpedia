-- Prove2me | Theorems.Thm_PI_EF_kb_le_of_le
-- name    : PI.EF.kb_le_of_le
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T05:28:52.90415+00:00
-- url     : https://prove2.me/theorems/955b252f-15bf-5b12-9c16-3d58d5012ac4
-- title:
--   EF: kb le of le
-- statement:
--   The EF construction uses the kb le of le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ExplicitFormula/PerronSum.lean#L86-L95
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ExplicitFormula/PerronSum.lean#L86-L95

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExplicitFormula_GoodHeightExists
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExplicitFormula_PerronSum
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.EF
open Finset

theorem PI.EF.kb_le_of_le {T d y : ℝ} (hT : 0 < T) (hd : 0 < d) (h : d ≤ |Real.log y|) :
    kb T y ≤ 2 / (T * d) := by sorry
