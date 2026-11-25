-- Prove2me | Theorems.Thm_PI_RhsWLim_W_HU_range_inc
-- name    : PI.RhsWLim.W.HU.range_inc
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T08:26:53.719717+00:00
-- url     : https://prove2.me/theorems/77efdb30-d043-546f-a4f3-a1d26e9a0c13
-- title:
--   HU: range inc
-- statement:
--   The HU construction uses the range inc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeightedLimitGauge/HaarUniq.lean#L164-L164
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeightedLimitGauge/HaarUniq.lean#L164-L164

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

theorem PI.RhsWLim.W.HU.range_inc : Set.range (inc : Gp k r → Mt k r) = amb k r := by sorry
