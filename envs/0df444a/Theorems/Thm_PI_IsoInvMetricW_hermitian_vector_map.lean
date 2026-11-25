-- Prove2me | Theorems.Thm_PI_IsoInvMetricW_hermitian_vector_map
-- name    : PI.IsoInvMetricW.hermitian_vector_map
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T08:13:00.955391+00:00
-- url     : https://prove2.me/theorems/866fd970-9ecc-5783-9b6c-6f232c7d27e1
-- title:
--   Iso Inv Metric W: hermitian vector map
-- statement:
--   The Iso Inv Metric W construction uses the hermitian vector map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/InvariantMetricIsometry/HermitianVectorMap.lean#L17-L34
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/InvariantMetricIsometry/HermitianVectorMap.lean#L17-L34

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

theorem PI.IsoInvMetricW.hermitian_vector_map : HvMap := by sorry
