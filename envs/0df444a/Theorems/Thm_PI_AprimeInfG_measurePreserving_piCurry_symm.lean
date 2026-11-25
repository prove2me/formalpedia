-- Prove2me | Theorems.Thm_PI_AprimeInfG_measurePreserving_piCurry_symm
-- name    : PI.AprimeInfG.measurePreserving_piCurry_symm
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T08:07:06.931879+00:00
-- url     : https://prove2.me/theorems/7dc131e6-36a9-4d03-b09a-5535bfbe3597
-- title:
--   Aprime Inf G: measure Preserving pi Curry symm
-- statement:
--   The Aprime Inf G construction uses the measure Preserving pi Curry symm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ArchimedeanOrbitMeasures/PiCoord.lean#L10-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ArchimedeanOrbitMeasures/PiCoord.lean#L10-L26

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ArchimedeanOrbitMeasures_PiCoord
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

theorem PI.AprimeInfG.measurePreserving_piCurry_symm {V : Type} [Fintype V] {α : V → Type} [∀ v, Fintype (α v)]
    {X : ∀ v, α v → Type} [∀ v a, MeasurableSpace (X v a)] (μ : ∀ v a, Measure (X v a))
    [∀ v a, SigmaFinite (μ v a)] :
    MeasurePreserving (MeasurableEquiv.piCurry X).symm (Measure.pi fun v => Measure.pi fun a => μ v a)
      (Measure.pi fun p : Σ v, α v => μ p.1 p.2) := by sorry
