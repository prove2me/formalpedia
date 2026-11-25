-- Prove2me | Theorems.Thm_PI_ExistsGaugeMeasureForEachRank_W_v0_ne
-- name    : PI.ExistsGaugeMeasureForEachRank.W.v0_ne
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T08:18:36.310028+00:00
-- url     : https://prove2.me/theorems/093d7f87-914f-4e1d-ac9a-c5cdc19e850c
-- title:
--   W: v0 ne
-- statement:
--   The W construction uses the v0 ne property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/CircleGaugeAction/OfRealCoordsSmulCenterCoord.lean#L89-L93
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/CircleGaugeAction/OfRealCoordsSmulCenterCoord.lean#L89-L93

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

theorem PI.ExistsGaugeMeasureForEachRank.W.v0_ne : v0 r ≠ 0 := by sorry
