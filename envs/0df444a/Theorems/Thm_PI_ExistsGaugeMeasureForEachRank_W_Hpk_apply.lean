-- Prove2me | Theorems.Thm_PI_ExistsGaugeMeasureForEachRank_W_Hpk_apply
-- name    : PI.ExistsGaugeMeasureForEachRank.W.Hpk_apply
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T08:09:06.254794+00:00
-- url     : https://prove2.me/theorems/aa3b3e78-a544-54f2-af8b-52d8bbb2a8b7
-- title:
--   W: Hpk apply
-- statement:
--   The W construction uses the Hpk apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/CircleGaugeAction/DglApplyOff.lean#L36-L41
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/CircleGaugeAction/DglApplyOff.lean#L36-L41

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

theorem PI.ExistsGaugeMeasureForEachRank.W.Hpk_apply (p q : Fin (2 * r + 0 + 1)) :
    Hpk 0 r p q = if q = Fin.rev p then (if p = cI r then -1 else 1) else 0 := by sorry
