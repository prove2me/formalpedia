-- Prove2me | Theorems.Thm_PI_ExistsGaugeMeasureForEachRank_W_dgl_apply_off
-- name    : PI.ExistsGaugeMeasureForEachRank.W.dgl_apply_off
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T08:09:47.251379+00:00
-- url     : https://prove2.me/theorems/a18e5d89-f4c4-4689-be01-dc6b2f754447
-- title:
--   W: dgl apply off
-- statement:
--   The W construction uses the dgl apply off property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/CircleGaugeAction/DglApplyOff.lean#L21-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/CircleGaugeAction/DglApplyOff.lean#L21-L28

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

theorem PI.ExistsGaugeMeasureForEachRank.W.dgl_apply_off (u : ℂ) (i j : Fin (2 * r + 0 + 1)) (h : ¬ (i = cI r ∧ j = cI r)) :
    dgl r u i j = (1 : Mat 0 r) i j := by sorry
