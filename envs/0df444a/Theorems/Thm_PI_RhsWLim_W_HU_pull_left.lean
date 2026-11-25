-- Prove2me | Theorems.Thm_PI_RhsWLim_W_HU_pull_left
-- name    : PI.RhsWLim.W.HU.pull_left
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T08:26:45.8968+00:00
-- url     : https://prove2.me/theorems/ca8a8ad0-5884-4386-bbfd-643cdaf69952
-- title:
--   HU: pull left
-- statement:
--   The HU construction uses the pull left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeightedLimitGauge/HaarUniq.lean#L218-L238
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeightedLimitGauge/HaarUniq.lean#L218-L238

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

theorem PI.RhsWLim.W.HU.pull_left (μ : Measure (Mt k r)) (h : ∀ a ∈ UWb k r, μ.map (lmulM a) = μ) :
    (pull μ).IsMulLeftInvariant := by sorry
