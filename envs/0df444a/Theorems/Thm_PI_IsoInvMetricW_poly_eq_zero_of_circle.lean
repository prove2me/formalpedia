-- Prove2me | Theorems.Thm_PI_IsoInvMetricW_poly_eq_zero_of_circle
-- name    : PI.IsoInvMetricW.poly_eq_zero_of_circle
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T08:08:55.144699+00:00
-- url     : https://prove2.me/theorems/a997b984-b8e1-4bc0-97bc-d867daeb35cc
-- title:
--   Iso Inv Metric W: poly eq zero of circle
-- statement:
--   The Iso Inv Metric W construction uses the poly eq zero of circle property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/InvariantMetricIsometry/PolyEqZeroOfCircle.lean#L10-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/InvariantMetricIsometry/PolyEqZeroOfCircle.lean#L10-L22

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

theorem PI.IsoInvMetricW.poly_eq_zero_of_circle (P : ℂ[X]) (h : ∀ z : ℂ, ‖z‖ = 1 → P.eval z = 0) : P = 0 := by sorry
