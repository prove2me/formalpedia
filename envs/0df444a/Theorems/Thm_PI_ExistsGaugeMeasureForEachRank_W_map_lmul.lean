-- Prove2me | Theorems.Thm_PI_ExistsGaugeMeasureForEachRank_W_map_lmul
-- name    : PI.ExistsGaugeMeasureForEachRank.W.map_lmul
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T08:32:51.300684+00:00
-- url     : https://prove2.me/theorems/ddc3479a-7c63-5956-935b-a6ecb4abd9d1
-- title:
--   W: map lmul
-- statement:
--   The W construction uses the map lmul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/CircleGaugeAction/ContinuousLmulM.lean#L66-L82
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/CircleGaugeAction/ContinuousLmulM.lean#L66-L82

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

theorem PI.ExistsGaugeMeasureForEachRank.W.map_lmul (s : Mat 0 r) (hs : s ∈ UWb 0 r) : (μG r).map (lmulM s) = μG r := by sorry
