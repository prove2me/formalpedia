-- Prove2me | Theorems.Thm_PI_EF_kb_le_nearB
-- name    : PI.EF.kb_le_nearB
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T05:29:41.5748+00:00
-- url     : https://prove2.me/theorems/328d3426-7275-4942-a893-49ec30682ac7
-- title:
--   EF: kb le near B
-- statement:
--   The EF construction uses the kb le near B property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ExplicitFormula/PerronSumBound.lean#L129-L144
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ExplicitFormula/PerronSumBound.lean#L129-L144

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExplicitFormula_PerronSum
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExplicitFormula_PerronSumBound
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

theorem PI.EF.kb_le_nearB {u T : ℝ} (hu : 0 < u) (hT : 0 < T) {n : ℕ} (hn : 0 < n)
    (hn2 : (n : ℝ) < 2 * u) : kb T (u / n) ≤ nearB u T n := by sorry
