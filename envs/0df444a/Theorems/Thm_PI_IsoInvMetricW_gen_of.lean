-- Prove2me | Theorems.Thm_PI_IsoInvMetricW_gen_of
-- name    : PI.IsoInvMetricW.gen_of
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T08:13:42.833476+00:00
-- url     : https://prove2.me/theorems/59061bef-cb21-458f-87f9-cc5a4a58a961
-- title:
--   Iso Inv Metric W: gen of
-- statement:
--   The Iso Inv Metric W construction uses the gen of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/InvariantMetricIsometry/HvScalar.lean#L98-L120
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/InvariantMetricIsometry/HvScalar.lean#L98-L120

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_InvariantMetricIsometry_VnuMapZero
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_InvariantMetricIsometry_HvScalar
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

theorem PI.IsoInvMetricW.gen_of (hQ : QR) (hM : HvMap) : Gen := by sorry
