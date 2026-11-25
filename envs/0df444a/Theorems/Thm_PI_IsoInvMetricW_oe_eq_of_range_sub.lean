-- Prove2me | Theorems.Thm_PI_IsoInvMetricW_oe_eq_of_range_sub
-- name    : PI.IsoInvMetricW.oe_eq_of_range_sub
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T08:08:57.583951+00:00
-- url     : https://prove2.me/theorems/73a5b818-9d78-54ab-9fca-958845c97380
-- title:
--   Iso Inv Metric W: oe eq of range sub
-- statement:
--   The Iso Inv Metric W construction uses the oe eq of range sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/InvariantMetricIsometry/OeEqOfRangeSub.lean#L12-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/InvariantMetricIsometry/OeEqOfRangeSub.lean#L12-L26

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

theorem PI.IsoInvMetricW.oe_eq_of_range_sub {h N : ℕ} (I J : Fin h ↪o Fin N) (hs : ∀ i, ∃ k, J k = I i) :
    I = J := by sorry
