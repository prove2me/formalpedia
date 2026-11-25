-- Prove2me | Theorems.Thm_PI_ExistsGaugeMeasureForEachRank_W_col_fix
-- name    : PI.ExistsGaugeMeasureForEachRank.W.col_fix
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T08:10:09.756631+00:00
-- url     : https://prove2.me/theorems/8dab0389-fd9f-481d-a618-91e8fec9f5fa
-- title:
--   W: col fix
-- statement:
--   The W construction uses the col fix property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/CircleGaugeAction/DglApplyOff.lean#L74-L87
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/CircleGaugeAction/DglApplyOff.lean#L74-L87

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

theorem PI.ExistsGaugeMeasureForEachRank.W.col_fix {g : Mat 0 r} (hg : g ∈ UWb 0 r) (j : Fin (2 * r + 0 + 1)) (hj : j ≠ cI r)
    (i : Fin (2 * r + 0 + 1)) : g i j = if i = j then 1 else 0 := by sorry
