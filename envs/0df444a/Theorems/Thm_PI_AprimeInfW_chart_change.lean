-- Prove2me | Theorems.Thm_PI_AprimeInfW_chart_change
-- name    : PI.AprimeInfW.chart_change
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T08:06:42.938624+00:00
-- url     : https://prove2.me/theorems/f008dc8a-5c7a-5ca1-ae0f-52de826ac6cc
-- title:
--   Aprime Inf W: chart change
-- statement:
--   The Aprime Inf W construction uses the chart change property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ArchimedeanOrbitMeasures/ChartChg.lean#L9-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ArchimedeanOrbitMeasures/ChartChg.lean#L9-L22

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

theorem PI.AprimeInfW.chart_change {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [μ.IsAddHaarMeasure] {Y : Type} [MeasurableSpace Y]
    (m : Measure Y) (χ : E → Y) (V : Set E) (f : E → ℝ)
    (hχ : ∀ S ⊆ V, MeasurableSet S → m (χ '' S) = ∫⁻ x in S, ENNReal.ofReal (f x) ∂μ)
    (ψ : E → E) (ψ' : E → E →L[ℝ] E) (U : Set E) (hψ : ∀ x ∈ U, HasFDerivWithinAt ψ (ψ' x) U x)
    (hinj : Set.InjOn ψ U) (hψV : ψ '' U ⊆ V) (A : Set E) (hAU : A ⊆ U) (hA : MeasurableSet A) :
    m ((χ ∘ ψ) '' A) = ∫⁻ p in A, ENNReal.ofReal (|(ψ' p).det| * f (ψ p)) ∂μ := by sorry
