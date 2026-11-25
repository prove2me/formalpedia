-- Prove2me | Theorems.Thm_PI_IsoInvMetricW_vnuMap_torus
-- name    : PI.IsoInvMetricW.vnuMap_torus
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T08:08:46.573105+00:00
-- url     : https://prove2.me/theorems/d8147e28-f9d1-4340-8da3-cc37f22fae97
-- title:
--   Iso Inv Metric W: vnu Map torus
-- statement:
--   The Iso Inv Metric W construction uses the vnu Map torus property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/InvariantMetricIsometry/PolyEqZeroOfCircle.lean#L76-L82
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/InvariantMetricIsometry/PolyEqZeroOfCircle.lean#L76-L82

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

theorem PI.IsoInvMetricW.vnuMap_torus (z : ℂ) (φ : LaC N nu) (I : ColChoice N nu) :
    VnuMap nu (fun s => Matrix.diagonal (dz z s)) φ I = z ^ wt I * φ I := by sorry
