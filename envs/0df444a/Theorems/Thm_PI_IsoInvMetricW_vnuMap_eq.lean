-- Prove2me | Theorems.Thm_PI_IsoInvMetricW_vnuMap_eq
-- name    : PI.IsoInvMetricW.vnuMap_eq
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T02:48:04.605949+00:00
-- url     : https://prove2.me/theorems/4a80f3b7-6f26-43f6-8b1e-e343558f2820
-- title:
--   Iso Inv Metric W: vnu Map eq
-- statement:
--   The Iso Inv Metric W construction uses the vnu Map eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/InvariantMetricIsometry/VnuMapZero.lean#L15-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/InvariantMetricIsometry/VnuMapZero.lean#L15-L19

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

theorem PI.IsoInvMetricW.vnuMap_eq (f : Lt → Matrix (Fin N) (Fin N) ℂ) (φ : LaC N nu) (I : ColChoice N nu) :
    VnuMap nu f φ I = ∑ J, E nu f I J * φ J := by sorry
