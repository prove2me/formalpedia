-- Prove2me | Theorems.Thm_PI_RhsWLim_W_continuous_opEmap
-- name    : PI.RhsWLim.W.continuous_opEmap
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T08:34:02.58323+00:00
-- url     : https://prove2.me/theorems/230b7225-6fac-4b1a-806e-c9895867465c
-- title:
--   W: continuous op Emap
-- statement:
--   The W construction uses the continuous op Emap property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeightedLimitGauge/OrbitPushE.lean#L35-L47
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeightedLimitGauge/OrbitPushE.lean#L35-L47

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_RhsWLim
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_VolumeLieE
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_OrbitPushCut
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_OrbitPushE
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

theorem PI.RhsWLim.W.continuous_opEmap (k r : ℕ) (T' : ℝ) :
    Continuous (fun q : TrE k => opCo k r (NormedSpace.exp (opGen k r q) *ᵥ opBase k r T')) := by sorry
