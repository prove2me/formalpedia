-- Prove2me | Theorems.Thm_PI_ExistsGaugeMeasureForEachRank_W_entry_zero
-- name    : PI.ExistsGaugeMeasureForEachRank.W.entry_zero
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T08:18:01.331382+00:00
-- url     : https://prove2.me/theorems/5d574f1f-8ab4-5ccf-a804-068e0aefdca4
-- title:
--   W: entry zero
-- statement:
--   The W construction uses the entry zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/CircleGaugeAction/OfRealCoordsSmulCenterCoord.lean#L37-L53
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/CircleGaugeAction/OfRealCoordsSmulCenterCoord.lean#L37-L53

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
set_option backward.isDefEq.respectTransparency false
open scoped Norms.Operator

theorem PI.ExistsGaugeMeasureForEachRank.W.entry_zero {X : Mat 0 r} (hX : X ∈ lieOf (UWb 0 r)) (i j : Fin (2 * r + 0 + 1))
    (hij : ¬ (i = cI r ∧ j = cI r)) : X i j = 0 := by sorry
