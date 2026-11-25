-- Prove2me | Theorems.Thm_PI_RhsWLim_W_continuous_hq
-- name    : PI.RhsWLim.W.continuous_hq
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T08:59:42.439141+00:00
-- url     : https://prove2.me/theorems/3887845d-2ac9-5d94-8fb0-1b906221c2d0
-- title:
--   W: continuous hq
-- statement:
--   The W construction uses the continuous hq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeightedLimitGauge/OrbitPushH.lean#L18-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeightedLimitGauge/OrbitPushH.lean#L18-L24

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_RhsWLim
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_VolumeLieE
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_OrbitPushE
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_OrbitPushC
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_OrbitPushH
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
open PI PI.RhsWLim PI.RhsWLim.W
open PI.RhsWLim

theorem PI.RhsWLim.W.continuous_hq (k : ℕ) (T' : ℝ) : Continuous (fun p : (Fin k → ℂ) × ℝ => hq k T' p.1 p.2) := by sorry
