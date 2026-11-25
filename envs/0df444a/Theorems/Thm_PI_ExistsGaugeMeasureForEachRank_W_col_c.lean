-- Prove2me | Theorems.Thm_PI_ExistsGaugeMeasureForEachRank_W_col_c
-- name    : PI.ExistsGaugeMeasureForEachRank.W.col_c
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T08:09:35.021022+00:00
-- url     : https://prove2.me/theorems/d4709db6-aaf6-4052-8c80-415a974e8cce
-- title:
--   W: col c
-- statement:
--   The W construction uses the col c property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/CircleGaugeAction/DglApplyOff.lean#L93-L101
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/CircleGaugeAction/DglApplyOff.lean#L93-L101

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

theorem PI.ExistsGaugeMeasureForEachRank.W.col_c {g : Mat 0 r} (hg : g ∈ UWb 0 r) (q : Fin (2 * r + 0 + 1)) (hq : q ≠ cI r) :
    g q (cI r) = 0 := by sorry
