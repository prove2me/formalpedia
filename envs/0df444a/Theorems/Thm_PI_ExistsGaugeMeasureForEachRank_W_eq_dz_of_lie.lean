-- Prove2me | Theorems.Thm_PI_ExistsGaugeMeasureForEachRank_W_eq_dz_of_lie
-- name    : PI.ExistsGaugeMeasureForEachRank.W.eq_dz_of_lie
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T08:18:01.483615+00:00
-- url     : https://prove2.me/theorems/7a8412e0-7a70-5097-aef8-035120071e0c
-- title:
--   W: eq dz of lie
-- statement:
--   The W construction uses the eq dz of lie property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/CircleGaugeAction/OfRealCoordsSmulCenterCoord.lean#L55-L65
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/CircleGaugeAction/OfRealCoordsSmulCenterCoord.lean#L55-L65

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

theorem PI.ExistsGaugeMeasureForEachRank.W.eq_dz_of_lie {X : Mat 0 r} (hX : X ∈ lieOf (UWb 0 r)) : X = dz r (X (cI r) (cI r)) := by sorry
