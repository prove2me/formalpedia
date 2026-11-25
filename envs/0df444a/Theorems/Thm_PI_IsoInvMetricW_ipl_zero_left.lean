-- Prove2me | Theorems.Thm_PI_IsoInvMetricW_ipl_zero_left
-- name    : PI.IsoInvMetricW.ipl_zero_left
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T08:09:15.611294+00:00
-- url     : https://prove2.me/theorems/4b04d216-a113-5068-8a22-862bd76a7ba3
-- title:
--   Iso Inv Metric W: ipl zero left
-- statement:
--   The Iso Inv Metric W construction uses the ipl zero left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/InvariantMetricIsometry/SymmetricMeasureL2NormEqResolutionL2.lean#L21-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/InvariantMetricIsometry/SymmetricMeasureL2NormEqResolutionL2.lean#L21-L22

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_InvariantMetricIsometry_ColChoiceFintype
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_InvariantMetricIsometry_SymmetricMeasureL2NormEqResolutionL2
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open PI PI.IsoInvMetricW
open PI.IsoInvMetric
variable {Lt : Type} [Fintype Lt] [DecidableEq Lt] {N : ℕ} {nu : Lt → YoungDiagram}

theorem PI.IsoInvMetricW.ipl_zero_left (ψ : LaC N nu) : ipl 0 ψ = 0 := by sorry
