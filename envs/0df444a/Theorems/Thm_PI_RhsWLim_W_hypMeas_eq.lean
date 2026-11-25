-- Prove2me | Theorems.Thm_PI_RhsWLim_W_hypMeas_eq
-- name    : PI.RhsWLim.W.hypMeas_eq
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T08:26:48.76386+00:00
-- url     : https://prove2.me/theorems/ab73d8bb-78ea-41ef-a93c-b5b521180b82
-- title:
--   W: hyp Meas eq
-- statement:
--   The W construction uses the hyp Meas eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeightedLimitGauge/OrbitPushCut.lean#L96-L102
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeightedLimitGauge/OrbitPushCut.lean#L96-L102

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

theorem PI.RhsWLim.W.hypMeas_eq (k : ℕ) (T' : ℝ) {f : (Fin k → ℂ) × ℂ → ℝ≥0∞} (hf : Measurable f) :
    hypMeas k T' f = ∫⁻ p, f p ∂hypM k T' := by sorry
