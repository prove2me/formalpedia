-- Prove2me | Theorems.Thm_PI_IsoInvMetricW_vnuMap_add
-- name    : PI.IsoInvMetricW.vnuMap_add
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T08:08:49.155495+00:00
-- url     : https://prove2.me/theorems/5ebf1c60-3792-4056-9c94-0fe84f764b1f
-- title:
--   Iso Inv Metric W: vnu Map add
-- statement:
--   The Iso Inv Metric W construction uses the vnu Map add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/InvariantMetricIsometry/VnuMapZero.lean#L21-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/InvariantMetricIsometry/VnuMapZero.lean#L21-L24

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

theorem PI.IsoInvMetricW.vnuMap_add (f : Lt → Matrix (Fin N) (Fin N) ℂ) (φ ψ : LaC N nu) :
    VnuMap nu f (φ + ψ) = VnuMap nu f φ + VnuMap nu f ψ := by sorry
