-- Prove2me | Theorems.Thm_PI_ExistsGaugeMeasureForEachRank_W_vol_ball
-- name    : PI.ExistsGaugeMeasureForEachRank.W.vol_ball
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T08:25:43.925988+00:00
-- url     : https://prove2.me/theorems/248566ca-f48b-59ee-a2e7-1673c6e706e9
-- title:
--   W: vol ball
-- statement:
--   The W construction uses the vol ball property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/CircleGaugeAction/ContinuousLmulM.lean#L153-L163
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/CircleGaugeAction/ContinuousLmulM.lean#L153-L163

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

theorem PI.ExistsGaugeMeasureForEachRank.W.vol_ball {ρ : ℝ} (h0 : 0 ≤ ρ) :
    volume (Metric.ball (0 : lieE (UWb 0 r)) ρ) = ENNReal.ofReal (2 * ρ) := by sorry
