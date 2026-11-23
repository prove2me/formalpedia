-- Prove2me | Theorems.Thm_PI_IsoInvMetricW_sum_prod_cc
-- name    : PI.IsoInvMetricW.sum_prod_cc
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:31:12.168811+00:00
-- url     : https://prove2.me/theorems/315ba0c4-d8c3-42ff-b5ed-9ae78fa85055
-- title:
--   Iso Inv Metric W: sum prod cc
-- statement:
--   The Iso Inv Metric W construction uses the sum prod cc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/InvariantMetricIsometry/HermitianVectorMap.lean#L11-L15
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/InvariantMetricIsometry/HermitianVectorMap.lean#L11-L15

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

theorem PI.IsoInvMetricW.sum_prod_cc {Lt : Type} [Fintype Lt] [DecidableEq Lt] {N : ℕ} {nu : Lt → YoungDiagram}
    (F : ∀ (s : Lt) (c : Fin ((nu s).rowLen 0)), (Fin ((nu s).colLen c) ↪o Fin N) → ℂ) :
    ∑ J : ColChoice N nu, ∏ s, ∏ c, F s c (J s c) = ∏ s, ∏ c, ∑ K, F s c K := by sorry
