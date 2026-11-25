-- Prove2me | Theorems.Thm_PI_IsoInvMetricW_eStar
-- name    : PI.IsoInvMetricW.eStar
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T08:13:51.621352+00:00
-- url     : https://prove2.me/theorems/197cb7fc-50d7-497e-b066-9ab8f16153af
-- title:
--   Iso Inv Metric W: e Star
-- statement:
--   The Iso Inv Metric W construction uses the e Star property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/InvariantMetricIsometry/VnuMapZero.lean#L36-L42
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/InvariantMetricIsometry/VnuMapZero.lean#L36-L42

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_InvariantMetricIsometry_OeEqOfRangeSub
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_InvariantMetricIsometry_VnuMapZero
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
variable {Lt : Type} [Fintype Lt] [DecidableEq Lt] {N : ℕ} {nu : Lt → YoungDiagram}

theorem PI.IsoInvMetricW.eStar (k : Lt → Matrix (Fin N) (Fin N) ℂ) (I J : ColChoice N nu) :
    starRingEnd ℂ (E nu k I J) = E nu (fun s => star (k s)) J I := by sorry
