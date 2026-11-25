-- Prove2me | Theorems.Thm_PI_ExistsGaugeMeasureForEachRank_W_toCircle_coe
-- name    : PI.ExistsGaugeMeasureForEachRank.W.toCircle_coe
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T08:25:40.573827+00:00
-- url     : https://prove2.me/theorems/5deb77f2-d1b2-4bcd-84df-045b9e2969e5
-- title:
--   W: to Circle coe
-- statement:
--   The W construction uses the to Circle coe property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/CircleGaugeAction/ContinuousLmulM.lean#L20-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/CircleGaugeAction/ContinuousLmulM.lean#L20-L22

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

theorem PI.ExistsGaugeMeasureForEachRank.W.toCircle_coe (s : ℝ) :
    ((AddCircle.toCircle (s : AddCircle (2 * π)) : Circle) : ℂ) = Complex.exp (s * Complex.I) := by sorry
