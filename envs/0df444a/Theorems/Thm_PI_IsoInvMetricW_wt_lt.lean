-- Prove2me | Theorems.Thm_PI_IsoInvMetricW_wt_lt
-- name    : PI.IsoInvMetricW.wt_lt
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T08:09:00.869387+00:00
-- url     : https://prove2.me/theorems/6e835198-d40e-5318-a1c5-18c7d5446d54
-- title:
--   Iso Inv Metric W: wt lt
-- statement:
--   The Iso Inv Metric W construction uses the wt lt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/InvariantMetricIsometry/PolyEqZeroOfCircle.lean#L49-L72
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/InvariantMetricIsometry/PolyEqZeroOfCircle.lean#L49-L72

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

theorem PI.IsoInvMetricW.wt_lt (hle : ∀ z, (nu z).colLen 0 ≤ N) (J : ColChoice N nu) (hJ : J ≠ J0 nu hle) :
    wt J < wt (J0 nu hle) := by sorry
