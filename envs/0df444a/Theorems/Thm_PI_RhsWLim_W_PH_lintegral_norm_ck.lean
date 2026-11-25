-- Prove2me | Theorems.Thm_PI_RhsWLim_W_PH_lintegral_norm_ck
-- name    : PI.RhsWLim.W.PH.lintegral_norm_ck
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T08:27:13.618908+00:00
-- url     : https://prove2.me/theorems/169d41cf-25c6-4651-bf66-7dd5329fe690
-- title:
--   PH: lintegral norm ck
-- statement:
--   The PH construction uses the lintegral norm ck property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeightedLimitGauge/PolarHyp.lean#L43-L63
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeightedLimitGauge/PolarHyp.lean#L43-L63

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_RhsWLim
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_VolumeLieE
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_PolarHyp
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
open MeasureTheory Filter Topology Set
open scoped ENNReal
open PI PI.RhsWLim PI.RhsWLim.W PI.RhsWLim.W.PH

theorem PI.RhsWLim.W.PH.lintegral_norm_ck (k : ℕ) (hk : 1 ≤ k) (F : ℝ → ℝ≥0∞) (hF : Measurable F) :
    ∫⁻ y : EuclideanSpace ℂ (Fin k), F ‖y‖ = ENNReal.ofReal (2 * Real.pi ^ k / (k - 1).factorial) *
      ∫⁻ ρ in Ioi (0 : ℝ), ENNReal.ofReal (ρ ^ (2 * k - 1)) * F ρ := by sorry
