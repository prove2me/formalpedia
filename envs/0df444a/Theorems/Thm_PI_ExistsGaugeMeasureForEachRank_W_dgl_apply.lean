-- Prove2me | Theorems.Thm_PI_ExistsGaugeMeasureForEachRank_W_dgl_apply
-- name    : PI.ExistsGaugeMeasureForEachRank.W.dgl_apply
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T08:09:33.497566+00:00
-- url     : https://prove2.me/theorems/308fd072-d65e-4a3e-a2d7-847d34f76a9e
-- title:
--   W: dgl apply
-- statement:
--   The W construction uses the dgl apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/CircleGaugeAction/DglApplyOff.lean#L16-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/CircleGaugeAction/DglApplyOff.lean#L16-L19

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

theorem PI.ExistsGaugeMeasureForEachRank.W.dgl_apply (u : ℂ) (i j : Fin (2 * r + 0 + 1)) :
    dgl r u i j = if i = j then (if i = cI r then u else 1) else 0 := by sorry
