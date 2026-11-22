-- Prove2me | Theorems.Thm_PI_QnHermHaar_Gen_repOn_sub
-- name    : PI.QnHermHaar.Gen.repOn_sub
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T21:00:44.070061+00:00
-- url     : https://prove2.me/theorems/67ec9537-8dd3-43b8-817e-8ca02b10dc4b
-- title:
--   Gen: rep On sub
-- statement:
--   The Gen construction uses the rep On sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/HermitianHaarMeasure/RepOnAlgebraMap.lean#L383-L390
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/HermitianHaarMeasure/RepOnAlgebraMap.lean#L383-L390

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HermitianHaarMeasure_RepOnAlgebraMap
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory
noncomputable section
open PI PI.QnHermHaar PI.QnHermHaar.Gen
variable {α β : Type*} [MeasurableSpace α]
variable {μ : Measure α} {ι : α → β} {𝓕 : Submodule ℂ (β → ℂ)}
variable (hI : IntOn μ ι 𝓕)
variable (G : Set β) (hG : ∀ᵐ x ∂μ, ι x ∈ G)
variable {G}
variable (hG : ∀ᵐ x ∂μ, ι x ∈ G)

theorem PI.QnHermHaar.Gen.repOn_sub {S T : A hI} {Φ Ψ : (β → ℂ) → β → ℂ} (hS : RepOn hI S Φ) (hT : RepOn hI T Ψ) :
    RepOn hI (S - T) (fun f => Φ f - Ψ f) := by sorry
