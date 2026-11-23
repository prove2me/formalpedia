-- Prove2me | Theorems.Thm_PI_AprimeInfG_lintegral_fintype_prod
-- name    : PI.AprimeInfG.lintegral_fintype_prod
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T08:15:32.784766+00:00
-- url     : https://prove2.me/theorems/a2820e8a-01fb-4868-84e6-f7f379ab36ee
-- title:
--   Aprime Inf G: lintegral fintype prod
-- statement:
--   The Aprime Inf G construction uses the lintegral fintype prod property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ArchimedeanOrbitMeasures/PiDens.lean#L44-L59
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ArchimedeanOrbitMeasures/PiDens.lean#L44-L59

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ArchimedeanOrbitMeasures_PiDens
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.AprimeInfG
open MeasureTheory Set
open scoped ENNReal

theorem PI.AprimeInfG.lintegral_fintype_prod {ι : Type} [Fintype ι] {E : ι → Type} {mE : ∀ i, MeasurableSpace (E i)}
    {μ : (i : ι) → Measure (E i)} [∀ i, SigmaFinite (μ i)] (f : (i : ι) → E i → ℝ≥0∞)
    (hf : ∀ i, Measurable (f i)) :
    ∫⁻ x : (i : ι) → E i, ∏ i, f i (x i) ∂(Measure.pi μ) = ∏ i, ∫⁻ x, f i x ∂(μ i) := by sorry
