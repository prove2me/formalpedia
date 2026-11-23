-- Prove2me | Theorems.Thm_PI_IsoInvMetricW_star_mul_self_of_norm
-- name    : PI.IsoInvMetricW.star_mul_self_of_norm
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:30:54.426804+00:00
-- url     : https://prove2.me/theorems/a430491e-6efc-4480-b594-bdc5a49bb8a1
-- title:
--   Iso Inv Metric W: star mul self of norm
-- statement:
--   The Iso Inv Metric W construction uses the star mul self of norm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/InvariantMetricIsometry/PolyEqZeroOfCircle.lean#L24-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/InvariantMetricIsometry/PolyEqZeroOfCircle.lean#L24-L27

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_InvariantMetricIsometry_VnuMapZero
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_InvariantMetricIsometry_PolyEqZeroOfCircle
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Classical Finset PI.IsoInvMetric Polynomial
open PI PI.IsoInvMetricW

theorem PI.IsoInvMetricW.star_mul_self_of_norm {z : ℂ} (hz : ‖z‖ = 1) : star z * z = 1 := by sorry
