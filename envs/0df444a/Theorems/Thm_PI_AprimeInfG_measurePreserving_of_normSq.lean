-- Prove2me | Theorems.Thm_PI_AprimeInfG_measurePreserving_of_normSq
-- name    : PI.AprimeInfG.measurePreserving_of_normSq
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T10:08:26.476686+00:00
-- url     : https://prove2.me/theorems/f2e7e1f8-bbb7-4587-a3d3-f83185f6cd0b
-- title:
--   Aprime Inf G: measure Preserving of norm Sq
-- statement:
--   The Aprime Inf G construction uses the measure Preserving of norm Sq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ArchimedeanOrbitMeasures/PiCoord.lean#L28-L88
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ArchimedeanOrbitMeasures/PiCoord.lean#L28-L88

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

theorem PI.AprimeInfG.measurePreserving_of_normSq {ι V : Type} [Fintype ι] [Fintype V] {α : V → Type} [∀ v, Fintype (α v)]
    (T : EuclideanSpace ℝ ι →ₗ[ℝ] (∀ v, EuclideanSpace ℝ (α v))) (hbij : Function.Bijective T)
    (hn : ∀ x, ∑ v, ‖T x v‖ ^ 2 = ‖x‖ ^ 2) :
    MeasurePreserving T volume (Measure.pi fun _ => volume) := by sorry
