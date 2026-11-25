-- Prove2me | Theorems.Thm_PI_ExistsGaugeMeasureForEachRank_W_dgl_norm
-- name    : PI.ExistsGaugeMeasureForEachRank.W.dgl_norm
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T08:10:20.722938+00:00
-- url     : https://prove2.me/theorems/40405f99-6680-4325-8f69-0306f5d8ebc5
-- title:
--   W: dgl norm
-- statement:
--   The W construction uses the dgl norm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/CircleGaugeAction/DglApplyOff.lean#L119-L129
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/CircleGaugeAction/DglApplyOff.lean#L119-L129

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

theorem PI.ExistsGaugeMeasureForEachRank.W.dgl_norm {u : ℂ} (h : dgl r u ∈ UWb 0 r) : (starRingEnd ℂ) u * u = 1 := by sorry
