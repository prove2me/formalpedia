-- Prove2me | Theorems.Thm_PI_RhsWLim_W_opBase_last
-- name    : PI.RhsWLim.W.opBase_last
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T08:51:43.544324+00:00
-- url     : https://prove2.me/theorems/27c1db31-3791-4bed-9451-53e1369d43c6
-- title:
--   W: op Base last
-- statement:
--   The W construction uses the op Base last property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeightedLimitGauge/PhiDiff.lean#L56-L57
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeightedLimitGauge/PhiDiff.lean#L56-L57

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_OrbitPushLoc
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_PhiDiff
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix NormedSpace
open PI PI.RhsWLim PI.RhsWLim.W
open PI.RhsWLim
attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra
variable {k r : ℕ}

theorem PI.RhsWLim.W.opBase_last (T' : ℝ) : opBase k r T' (wI k r (Fin.last k)) = (Real.sqrt T' : ℂ) := by sorry
