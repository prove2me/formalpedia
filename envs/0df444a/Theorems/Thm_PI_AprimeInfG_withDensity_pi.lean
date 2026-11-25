-- Prove2me | Theorems.Thm_PI_AprimeInfG_withDensity_pi
-- name    : PI.AprimeInfG.withDensity_pi
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T05:23:20.043896+00:00
-- url     : https://prove2.me/theorems/f30083be-647a-5d98-8828-f4c8f3a7d533
-- title:
--   Aprime Inf G: with Density pi
-- statement:
--   The Aprime Inf G construction uses the with Density pi property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ArchimedeanOrbitMeasures/PiDens.lean#L61-L84
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ArchimedeanOrbitMeasures/PiDens.lean#L61-L84

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

theorem PI.AprimeInfG.withDensity_pi {ι : Type} [Fintype ι] {E : ι → Type} [∀ i, MeasurableSpace (E i)]
    (lam : (i : ι) → Measure (E i)) [∀ i, SigmaFinite (lam i)] (D : (i : ι) → E i → ℝ)
    (hD : ∀ i, Measurable (D i)) :
    (Measure.pi lam).withDensity (fun z => ∏ i, ENNReal.ofReal (D i (z i))) =
      Measure.pi (fun i => (lam i).withDensity (fun x => ENNReal.ofReal (D i x))) := by sorry
