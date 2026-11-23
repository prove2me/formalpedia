-- Prove2me | Theorems.Thm_PI_IsoInvMetricW_hvCols_of
-- name    : PI.IsoInvMetricW.hvCols_of
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:30:47.347723+00:00
-- url     : https://prove2.me/theorems/9480583d-8803-45db-8f30-f126522291f9
-- title:
--   Iso Inv Metric W: hv Cols of
-- statement:
--   The Iso Inv Metric W construction uses the hv Cols of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/InvariantMetricIsometry/VnuMapZero.lean#L64-L73
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/InvariantMetricIsometry/VnuMapZero.lean#L64-L73

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

theorem PI.IsoInvMetricW.hvCols_of (hM : HvMap) : HvCols := by sorry
