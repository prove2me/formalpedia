-- Prove2me | Theorems.Thm_PI_ExistsGaugeMeasureForEachRank_W_ofRealCoords_smul_centerCoord
-- name    : PI.ExistsGaugeMeasureForEachRank.W.ofRealCoords_smul_centerCoord
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T08:18:14.7248+00:00
-- url     : https://prove2.me/theorems/59d5a565-5604-5cfa-ba56-867a8b3caa4e
-- title:
--   W: of Real Coords smul center Coord
-- statement:
--   The W construction uses the of Real Coords smul center Coord property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/CircleGaugeAction/OfRealCoordsSmulCenterCoord.lean#L108-L130
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/CircleGaugeAction/OfRealCoordsSmulCenterCoord.lean#L108-L130

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_ExistsGaugeMeasureForEachRank
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CircleGaugeAction_DglApplyOff
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CircleGaugeAction_OfRealCoordsSmulCenterCoord
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Filter Topology
open PI PI.ExistsGaugeMeasureForEachRank PI.ExistsGaugeMeasureForEachRank.W
variable {r : ℕ}

theorem PI.ExistsGaugeMeasureForEachRank.W.ofRealCoords_smul_centerCoord (s : ℝ) : unrealify (s • v0 r) = dz r ((s : ℂ) * Complex.I) := by sorry
