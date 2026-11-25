-- Prove2me | Theorems.Thm_PI_RhsWLim_W_HU_pull_apply
-- name    : PI.RhsWLim.W.HU.pull_apply
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T08:26:36.182805+00:00
-- url     : https://prove2.me/theorems/fd133814-cfcf-51b8-abc1-c4d4175957b9
-- title:
--   HU: pull apply
-- statement:
--   The HU construction uses the pull apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeightedLimitGauge/HaarUniq.lean#L206-L209
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeightedLimitGauge/HaarUniq.lean#L206-L209

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_RhsWLim
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_VolumeLieE
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_HaarUniq
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option linter.unusedVariables false
noncomputable section
open MeasureTheory Filter Topology Matrix
open scoped ENNReal
open PI PI.RhsWLim PI.RhsWLim.W PI.RhsWLim.W.HU
open PI.RhsWLim
variable {k r : ℕ}

theorem PI.RhsWLim.W.HU.pull_apply (μ : Measure (Mt k r)) (h : μ {x | Matrix.of x ∉ UWb k r} = 0) (s : Set (Mt k r)) :
    pull μ (inc ⁻¹' s) = μ s := by sorry
