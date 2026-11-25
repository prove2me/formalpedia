-- Prove2me | Theorems.Thm_PI_ExistsGaugeMeasureForEachRank_W_mem_UWb_iff
-- name    : PI.ExistsGaugeMeasureForEachRank.W.mem_UWb_iff
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T08:09:51.028193+00:00
-- url     : https://prove2.me/theorems/7c7bdf98-541d-4495-9abc-e02046e40415
-- title:
--   W: mem UWb iff
-- statement:
--   The W construction uses the mem UWb iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/CircleGaugeAction/DglApplyOff.lean#L131-L138
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/CircleGaugeAction/DglApplyOff.lean#L131-L138

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_ExistsGaugeMeasureForEachRank
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CircleGaugeAction_DglApplyOff
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open PI PI.ExistsGaugeMeasureForEachRank PI.ExistsGaugeMeasureForEachRank.W
variable {r : ℕ}

theorem PI.ExistsGaugeMeasureForEachRank.W.mem_UWb_iff (g : Mat 0 r) :
    g ∈ UWb 0 r ↔ ∃ u : ℂ, (starRingEnd ℂ) u * u = 1 ∧ g = dgl r u := by sorry
