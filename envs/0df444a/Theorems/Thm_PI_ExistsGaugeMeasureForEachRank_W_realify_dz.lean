-- Prove2me | Theorems.Thm_PI_ExistsGaugeMeasureForEachRank_W_realify_dz
-- name    : PI.ExistsGaugeMeasureForEachRank.W.realify_dz
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T08:18:07.818037+00:00
-- url     : https://prove2.me/theorems/4d7802ed-d047-59a4-9242-01794e87cd71
-- title:
--   W: realify dz
-- statement:
--   The W construction uses the realify dz property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/CircleGaugeAction/OfRealCoordsSmulCenterCoord.lean#L95-L106
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/CircleGaugeAction/OfRealCoordsSmulCenterCoord.lean#L95-L106

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

theorem PI.ExistsGaugeMeasureForEachRank.W.realify_dz (s : ℝ) :
    (WithLp.equiv 2 _).symm (realifyFun (dz r ((s : ℂ) * Complex.I))) = s • v0 r := by sorry
