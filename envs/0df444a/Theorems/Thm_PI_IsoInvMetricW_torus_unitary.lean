-- Prove2me | Theorems.Thm_PI_IsoInvMetricW_torus_unitary
-- name    : PI.IsoInvMetricW.torus_unitary
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T08:09:19.23581+00:00
-- url     : https://prove2.me/theorems/cb8c4e61-9c33-4e35-8c73-358669ce35fb
-- title:
--   Iso Inv Metric W: torus unitary
-- statement:
--   The Iso Inv Metric W construction uses the torus unitary property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/InvariantMetricIsometry/PolyEqZeroOfCircle.lean#L84-L91
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/InvariantMetricIsometry/PolyEqZeroOfCircle.lean#L84-L91

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
variable {Lt : Type} [Fintype Lt] [DecidableEq Lt] {N : ℕ} {nu : Lt → YoungDiagram}

theorem PI.IsoInvMetricW.torus_unitary {z : ℂ} (hz : ‖z‖ = 1) (s : Lt) :
    Matrix.diagonal (dz (N := N) z s) ∈ Matrix.unitaryGroup (Fin N) ℂ := by sorry
