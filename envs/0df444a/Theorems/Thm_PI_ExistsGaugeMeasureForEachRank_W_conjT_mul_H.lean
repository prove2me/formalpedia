-- Prove2me | Theorems.Thm_PI_ExistsGaugeMeasureForEachRank_W_conjT_mul_H
-- name    : PI.ExistsGaugeMeasureForEachRank.W.conjT_mul_H
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T08:09:48.240429+00:00
-- url     : https://prove2.me/theorems/593156dd-fbae-41d2-a54c-59124063fb7b
-- title:
--   W: conj T mul H
-- statement:
--   The W construction uses the conj T mul H property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/CircleGaugeAction/DglApplyOff.lean#L89-L91
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/CircleGaugeAction/DglApplyOff.lean#L89-L91

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

theorem PI.ExistsGaugeMeasureForEachRank.W.conjT_mul_H {g : Mat 0 r} (hg : g ∈ UWb 0 r) (p : Fin (2 * r + 0 + 1)) (hp : p ≠ cI r)
    (k : Fin (2 * r + 0 + 1)) : (gᴴ * Hpk 0 r) p k = Hpk 0 r p k := by sorry
