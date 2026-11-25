-- Prove2me | Theorems.Thm_PI_ExistsGaugeMeasureForEachRank_W_conj_mul_iff
-- name    : PI.ExistsGaugeMeasureForEachRank.W.conj_mul_iff
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T08:09:30.405427+00:00
-- url     : https://prove2.me/theorems/3b29d7c3-6896-4b70-b04b-b28fd5032995
-- title:
--   W: conj mul iff
-- statement:
--   The W construction uses the conj mul iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/CircleGaugeAction/DglApplyOff.lean#L140-L143
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/CircleGaugeAction/DglApplyOff.lean#L140-L143

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

theorem PI.ExistsGaugeMeasureForEachRank.W.conj_mul_iff (u : ℂ) : (starRingEnd ℂ) u * u = 1 ↔ ‖u‖ = 1 := by sorry
