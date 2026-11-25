-- Prove2me | Theorems.Thm_PI_RhsWLim_W_PH_lintegral_fun_norm
-- name    : PI.RhsWLim.W.PH.lintegral_fun_norm
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T08:27:30.037418+00:00
-- url     : https://prove2.me/theorems/e4fa2508-014d-456d-aa36-b636aaf9e9c5
-- title:
--   PH: lintegral fun norm
-- statement:
--   The PH construction uses the lintegral fun norm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeightedLimitGauge/PolarHyp.lean#L14-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeightedLimitGauge/PolarHyp.lean#L14-L37

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

theorem PI.RhsWLim.W.PH.lintegral_fun_norm {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] [Nontrivial E] (μ : Measure E) [μ.IsAddHaarMeasure]
    (F : ℝ → ℝ≥0∞) (hF : Measurable F) :
    ∫⁻ x, F ‖x‖ ∂μ = μ.toSphere univ *
      ∫⁻ y in Ioi (0 : ℝ), ENNReal.ofReal (y ^ (Module.finrank ℝ E - 1)) * F y := by sorry
