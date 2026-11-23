-- Prove2me | Theorems.Thm_P2M_PI_QnHermHaar_Gen_toA_mk__50be6af2c076
-- name    : P2M_PI_QnHermHaar_Gen_toA_mk__50be6af2c076
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:11:56.801799+00:00
-- url     : https://prove2.me/theorems/dc55fdb6-b912-4185-9f58-746fd1f33111
-- title:
--   P2 M PI Qn Herm Haar Gen to A mk  50be6af2c076: P2 M PI Qn Herm Haar Gen to A mk  50be6af2c076
-- statement:
--   The P2 M PI Qn Herm Haar Gen to A mk  50be6af2c076 construction uses the P2 M PI Qn Herm Haar Gen to A mk  50be6af2c076 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/HermitianHaarMeasure/RepOnAlgebraMap.lean#L346-L347
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/HermitianHaarMeasure/RepOnAlgebraMap.lean#L346-L347

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

theorem P2M_PI_QnHermHaar_Gen_toA_mk__50be6af2c076 {Φ Φ' : (β → ℂ) → (β → ℂ)} (hΦ : AdjOp (μ := μ) (ι := ι) (𝓕 := 𝓕) G Φ Φ')
    {f : β → ℂ} (hf : f ∈ 𝓕) : ((toA hI hG hΦ : A hI) : Module.End ℂ (X hI)) (mk' hI f) = mk' hI (Φ f) := by sorry

alias «PI».«QnHermHaar».«Gen».«toA_mk'» := P2M_PI_QnHermHaar_Gen_toA_mk__50be6af2c076
