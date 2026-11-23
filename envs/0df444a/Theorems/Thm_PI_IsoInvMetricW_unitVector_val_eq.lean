-- Prove2me | Theorems.Thm_PI_IsoInvMetricW_unitVector_val_eq
-- name    : PI.IsoInvMetricW.unitVector_val_eq
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T08:30:57.633422+00:00
-- url     : https://prove2.me/theorems/6d99a5b3-f7af-4ef7-b367-eb84192113f0
-- title:
--   Iso Inv Metric W: unit Vector val eq
-- statement:
--   The Iso Inv Metric W construction uses the unit Vector val eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/InvariantMetricIsometry/OeEqOfRangeSub.lean#L59-L72
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/InvariantMetricIsometry/OeEqOfRangeSub.lean#L59-L72

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_InvariantMetricIsometry_ColChoiceFintype
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_InvariantMetricIsometry_OeEqOfRangeSub
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

theorem PI.IsoInvMetricW.unitVector_val_eq {Lt : Type} [Fintype Lt] [DecidableEq Lt] {N : ℕ} (nu : Lt → YoungDiagram)
    (hle : ∀ z, (nu z).colLen 0 ≤ N) (J : ColChoice N nu) :
    u0 N nu J = if J = J0 nu hle then 1 else 0 := by sorry
