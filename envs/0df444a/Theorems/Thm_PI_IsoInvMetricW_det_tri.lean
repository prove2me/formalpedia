-- Prove2me | Theorems.Thm_PI_IsoInvMetricW_det_tri
-- name    : PI.IsoInvMetricW.det_tri
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T08:10:30.637344+00:00
-- url     : https://prove2.me/theorems/6acf3958-e5ab-449a-bacb-1971957db7d5
-- title:
--   Iso Inv Metric W: det tri
-- statement:
--   The Iso Inv Metric W construction uses the det tri property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/InvariantMetricIsometry/HvScalar.lean#L25-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/InvariantMetricIsometry/HvScalar.lean#L25-L36

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

theorem PI.IsoInvMetricW.det_tri {h N : ℕ} (J : Fin h ↪o Fin N) (w : Fin N → ℕ → ℂ)
    (hw : ∀ (a : Fin N) (j : ℕ), j < a → w a j = 0) :
    Matrix.det (Matrix.of fun i j : Fin h => w (J i) (j : ℕ)) = ∏ i : Fin h, w (J i) i := by sorry
