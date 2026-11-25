-- Prove2me | Theorems.Thm_PI_AprimeInfW_chart_change_cont
-- name    : PI.AprimeInfW.chart_change_cont
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T08:07:01.239708+00:00
-- url     : https://prove2.me/theorems/ad6fbdcc-5c86-41ec-815d-9a08e9591c9f
-- title:
--   Aprime Inf W: chart change cont
-- statement:
--   The Aprime Inf W construction uses the chart change cont property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ArchimedeanOrbitMeasures/ChartChg.lean#L24-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ArchimedeanOrbitMeasures/ChartChg.lean#L24-L27

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ArchimedeanOrbitMeasures_ChartChg
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.AprimeInfW
open MeasureTheory Topology

theorem PI.AprimeInfW.chart_change_cont {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (f : E → ℝ) (ψ : E → E) (ψ' : E → E →L[ℝ] E) (x₀ : E) (hψ : ContinuousAt ψ x₀)
    (hf : ContinuousAt f (ψ x₀)) (hd : ContinuousAt (fun p => (ψ' p).det) x₀) :
    ContinuousAt (fun p => |(ψ' p).det| * f (ψ p)) x₀ := by sorry
