-- Prove2me | Theorems.Thm_PI_RhsWLim_W_continuous_hypPar
-- name    : PI.RhsWLim.W.continuous_hypPar
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T08:27:04.204383+00:00
-- url     : https://prove2.me/theorems/c72cf863-1fe8-41d7-9769-cb1a315be87a
-- title:
--   W: continuous hyp Par
-- statement:
--   The W construction uses the continuous hyp Par property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeightedLimitGauge/OrbitPushCut.lean#L92-L94
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeightedLimitGauge/OrbitPushCut.lean#L92-L94

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_RhsWLim
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_VolumeLieE
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_OrbitPushCut
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology Matrix
open scoped ENNReal
open PI PI.RhsWLim PI.RhsWLim.W
open PI.RhsWLim
variable {k r : ℕ}

theorem PI.RhsWLim.W.continuous_hypPar (k : ℕ) (T' : ℝ) : Continuous (hypPar k T') := by sorry
