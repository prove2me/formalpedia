-- Prove2me | Theorems.Thm_PI_RhsWLim_W_measurableSet_coneSh
-- name    : PI.RhsWLim.W.measurableSet_coneSh
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T09:05:27.929324+00:00
-- url     : https://prove2.me/theorems/00ce9328-1108-43c0-99f3-23a1c23b9d66
-- title:
--   W: measurable Set cone Sh
-- statement:
--   The W construction uses the measurable Set cone Sh property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeightedLimitGauge/OrbitPushV.lean#L65-L73
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeightedLimitGauge/OrbitPushV.lean#L65-L73

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_RhsWLim
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_VolumeLieE
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_OrbitPushH
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_OrbitPushV
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
variable {k : ℕ}

theorem PI.RhsWLim.W.measurableSet_coneSh {T' : ℝ} (hT' : 0 < T') {E : Set ((Fin k → ℂ) × ℂ)} (hE : MeasurableSet E) :
    MeasurableSet (coneSh k T' E) := by sorry
