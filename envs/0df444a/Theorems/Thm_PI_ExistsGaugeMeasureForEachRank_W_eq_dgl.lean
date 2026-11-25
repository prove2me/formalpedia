-- Prove2me | Theorems.Thm_PI_ExistsGaugeMeasureForEachRank_W_eq_dgl
-- name    : PI.ExistsGaugeMeasureForEachRank.W.eq_dgl
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T08:09:55.79915+00:00
-- url     : https://prove2.me/theorems/9e74a8a2-e33c-56b4-9ba2-bea9d0c22ca1
-- title:
--   W: eq dgl
-- statement:
--   The W construction uses the eq dgl property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/CircleGaugeAction/DglApplyOff.lean#L103-L117
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/CircleGaugeAction/DglApplyOff.lean#L103-L117

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

theorem PI.ExistsGaugeMeasureForEachRank.W.eq_dgl {g : Mat 0 r} (hg : g ∈ UWb 0 r) : g = dgl r (g (cI r) (cI r)) := by sorry
