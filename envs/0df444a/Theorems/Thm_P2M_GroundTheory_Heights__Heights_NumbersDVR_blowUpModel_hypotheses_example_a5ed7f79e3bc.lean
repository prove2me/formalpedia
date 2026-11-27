-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_blowUpModel_hypotheses_example_a5ed7f79e3bc
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_blowUpModel_hypotheses_example_a5ed7f79e3bc
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T13:33:37.016489+00:00
-- url     : https://prove2.me/theorems/12450989-fc33-40fc-a809-fa09c7a2e8c1
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR blow Up Model hypotheses example a5ed7f79e3bc: P2 M Ground Theory Heights  Heights Numbers DVR blow Up Model hypotheses example a5ed7f79e3bc
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR blow Up Model hypotheses example a5ed7f79e3bc construction uses the P2 M Ground Theory Heights  Heights Numbers DVR blow Up Model hypotheses example a5ed7f79e3bc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/CutIdentityRightSideCongrOfSubMem.lean#L308-L314
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/CutIdentityRightSideCongrOfSubMem.lean#L308-L314

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_SpanTwoIsPrimeRelevant
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_BundleObjects
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_CutIdentityRightSideCongrOfSubMem
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.NumbersDVR
open MvPolynomial
noncomputable section
universe u

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_blowUpModel_hypotheses_example_a5ed7f79e3bc :
    let S := MRing (fun _ : Unit => Fin 2) ℤ_[2]
    IsModelOver (⊥ : Ideal S) 1 ∧ (∀ j : Fin 2, IsMultiHomog (X ⟨(), j⟩ : S) (Pi.single () 1)) ∧
      ∃ j : Fin 2, (X ⟨(), j⟩ : S) ∉ (⊥ : Ideal S) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«blowUpModel_hypotheses_example» := P2M_GroundTheory_Heights__Heights_NumbersDVR_blowUpModel_hypotheses_example_a5ed7f79e3bc
