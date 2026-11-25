-- Prove2me | Theorems.Thm_PI_ExistsGaugeMeasureForEachRank_W_dgl_mem
-- name    : PI.ExistsGaugeMeasureForEachRank.W.dgl_mem
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T08:09:53.695809+00:00
-- url     : https://prove2.me/theorems/36caffa3-8527-42d2-900f-3c15dceacd15
-- title:
--   W: dgl mem
-- statement:
--   The W construction uses the dgl mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/CircleGaugeAction/DglApplyOff.lean#L43-L72
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/CircleGaugeAction/DglApplyOff.lean#L43-L72

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

theorem PI.ExistsGaugeMeasureForEachRank.W.dgl_mem {u : ℂ} (hu : (starRingEnd ℂ) u * u = 1) : dgl r u ∈ UWb 0 r := by sorry
