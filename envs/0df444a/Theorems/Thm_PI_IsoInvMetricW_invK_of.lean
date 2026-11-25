-- Prove2me | Theorems.Thm_PI_IsoInvMetricW_invK_of
-- name    : PI.IsoInvMetricW.invK_of
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T08:09:44.959906+00:00
-- url     : https://prove2.me/theorems/f35d435f-bca5-44af-878d-cd7ba2fc1e97
-- title:
--   Iso Inv Metric W: inv K of
-- statement:
--   The Iso Inv Metric W construction uses the inv K of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/InvariantMetricIsometry/VnuMapZero.lean#L109-L121
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/InvariantMetricIsometry/VnuMapZero.lean#L109-L121

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_InvariantMetricIsometry_OeEqOfRangeSub
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_InvariantMetricIsometry_VnuMapZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Classical
open PI PI.IsoInvMetricW
open PI.IsoInvMetric

theorem PI.IsoInvMetricW.invK_of (hE : EMul) : InvK := by sorry
