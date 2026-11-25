-- Prove2me | Theorems.Thm_PI_ExistsGaugeMeasureForEachRank_W_rev_eq_c_iff
-- name    : PI.ExistsGaugeMeasureForEachRank.W.rev_eq_c_iff
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T08:09:24.221867+00:00
-- url     : https://prove2.me/theorems/187365bc-f606-4d5d-8d24-92c0e94e9951
-- title:
--   W: rev eq c iff
-- statement:
--   The W construction uses the rev eq c iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/CircleGaugeAction/DglApplyOff.lean#L30-L34
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/CircleGaugeAction/DglApplyOff.lean#L30-L34

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

theorem PI.ExistsGaugeMeasureForEachRank.W.rev_eq_c_iff (p : Fin (2 * r + 0 + 1)) : Fin.rev p = cI r ↔ p = cI r := by sorry
