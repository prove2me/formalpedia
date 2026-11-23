-- Prove2me | Theorems.Thm_PI_IsoInvMetricW_vnuMap_smul
-- name    : PI.IsoInvMetricW.vnuMap_smul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:32:00.006004+00:00
-- url     : https://prove2.me/theorems/11f49e3d-cdad-4943-9f03-34df22bfc178
-- title:
--   Iso Inv Metric W: vnu Map smul
-- statement:
--   The Iso Inv Metric W construction uses the vnu Map smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/InvariantMetricIsometry/VnuMapZero.lean#L26-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/InvariantMetricIsometry/VnuMapZero.lean#L26-L30

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

theorem PI.IsoInvMetricW.vnuMap_smul (f : Lt → Matrix (Fin N) (Fin N) ℂ) (a : ℂ) (φ : LaC N nu) :
    VnuMap nu f (a • φ) = a • VnuMap nu f φ := by sorry
