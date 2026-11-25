-- Prove2me | Theorems.Thm_PI_IsoInvMetricW_metric_mul
-- name    : PI.IsoInvMetricW.metric_mul
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T08:08:58.599075+00:00
-- url     : https://prove2.me/theorems/26fc120c-7776-449a-9011-ac02d9cff563
-- title:
--   Iso Inv Metric W: metric mul
-- statement:
--   The Iso Inv Metric W construction uses the metric mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/InvariantMetricIsometry/HermitianVectorMap.lean#L36-L51
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/InvariantMetricIsometry/HermitianVectorMap.lean#L36-L51

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_InvariantMetricIsometry_ColChoiceFintype
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_InvariantMetricIsometry_MetricConstantBound
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_InvariantMetricIsometry_HermitianVectorMap
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Finset PI.IsoInvMetric
open PI PI.IsoInvMetricW

theorem PI.IsoInvMetricW.metric_mul : EMul := by sorry
