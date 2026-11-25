-- Prove2me | Theorems.Thm_PI_AprimeInfG_measurePreserving_piProdEquiv
-- name    : PI.AprimeInfG.measurePreserving_piProdEquiv
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T10:08:11.779623+00:00
-- url     : https://prove2.me/theorems/5be9b32b-0648-5110-a75a-9c9ee10ab93e
-- title:
--   Aprime Inf G: measure Preserving pi Prod Equiv
-- statement:
--   The Aprime Inf G construction uses the measure Preserving pi Prod Equiv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ArchimedeanOrbitMeasures/PiCoord.lean#L101-L119
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ArchimedeanOrbitMeasures/PiCoord.lean#L101-L119

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

theorem PI.AprimeInfG.measurePreserving_piProdEquiv {V : Type} [Fintype V] (A B : V → Type) [∀ v, MeasurableSpace (A v)]
    [∀ v, MeasurableSpace (B v)] (μ : ∀ v, Measure (A v)) (ν : ∀ v, Measure (B v)) [∀ v, SigmaFinite (μ v)]
    [∀ v, SigmaFinite (ν v)] :
    MeasurePreserving (piProdEquiv A B) (Measure.pi fun v => (μ v).prod (ν v))
      ((Measure.pi fun v => μ v).prod (Measure.pi fun v => ν v)) := by sorry
