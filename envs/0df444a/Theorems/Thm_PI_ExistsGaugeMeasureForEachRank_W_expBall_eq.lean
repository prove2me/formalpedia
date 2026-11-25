-- Prove2me | Theorems.Thm_PI_ExistsGaugeMeasureForEachRank_W_expBall_eq
-- name    : PI.ExistsGaugeMeasureForEachRank.W.expBall_eq
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T08:26:41.511034+00:00
-- url     : https://prove2.me/theorems/66fc1de4-8a1f-479c-8fa3-fe695622ce14
-- title:
--   W: exp Ball eq
-- statement:
--   The W construction uses the exp Ball eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/CircleGaugeAction/ContinuousLmulM.lean#L101-L129
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/CircleGaugeAction/ContinuousLmulM.lean#L101-L129

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_ExistsGaugeMeasureForEachRank
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CircleGaugeAction_DglApplyOff
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CircleGaugeAction_OfRealCoordsSmulCenterCoord
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CircleGaugeAction_ContinuousLmulM
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix MeasureTheory Filter Topology Set Real
open scoped ENNReal
open PI PI.ExistsGaugeMeasureForEachRank PI.ExistsGaugeMeasureForEachRank.W
variable {r : ℕ}

theorem PI.ExistsGaugeMeasureForEachRank.W.expBall_eq (ρ : ℝ) :
    expBall (UWb 0 r) ρ = Gm r '' (((↑) : ℝ → AddCircle (2 * π)) '' Ioo (-ρ) ρ) := by sorry
