-- Prove2me | Theorems.Thm_PI_RhsWLim_W_continuous_expChart
-- name    : PI.RhsWLim.W.continuous_expChart
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T08:26:12.066346+00:00
-- url     : https://prove2.me/theorems/8207745b-2db2-5605-b1df-02e2b4b09d60
-- title:
--   W: continuous exp Chart
-- statement:
--   The W construction uses the continuous exp Chart property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeightedLimitGauge/TBallMeas.lean#L14-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeightedLimitGauge/TBallMeas.lean#L14-L35

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_RhsWLim
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_VolumeLieE
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_TBallMeas
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

theorem PI.RhsWLim.W.continuous_expChart (k r : ℕ) (S : Set (Mat k r)) :
    Continuous (fun x : lieE S =>
      fun i j => NormedSpace.exp (unrealify (x : EuclideanSpace ℝ (Fin (2 * r + k + 1) × Fin (2 * r + k + 1) × Bool))) i j :
        lieE S → Mt k r) := by sorry
