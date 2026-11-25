-- Prove2me | Theorems.Thm_PI_RhsWLim_W_slice_mem
-- name    : PI.RhsWLim.W.slice_mem
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T09:05:46.818578+00:00
-- url     : https://prove2.me/theorems/46655ab0-27f1-44c6-9a93-c9f88f3b4185
-- title:
--   W: slice mem
-- statement:
--   The W construction uses the slice mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeightedLimitGauge/OrbitPushV.lean#L77-L116
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeightedLimitGauge/OrbitPushV.lean#L77-L116

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

theorem PI.RhsWLim.W.slice_mem {T' : ℝ} (hT' : 0 < T') (E : Set ((Fin k → ℂ) × ℂ)) (y : Fin k → ℂ) (θ t : ℝ) (ht : 0 < t) :
    (y, ((phiR (∑ i, Complex.normSq (y i)) T' t : ℝ) : ℂ) * Complex.exp (θ * Complex.I)) ∈ coneSh k T' E ↔
      (1 < t ∧ t < 2 ∧ hq k T' (t⁻¹ • y) θ ∈ E) := by sorry
