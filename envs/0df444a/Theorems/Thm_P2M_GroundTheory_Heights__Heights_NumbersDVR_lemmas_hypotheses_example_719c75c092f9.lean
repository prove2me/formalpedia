-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_lemmas_hypotheses_example_719c75c092f9
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_lemmas_hypotheses_example_719c75c092f9
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T04:11:13.852213+00:00
-- url     : https://prove2.me/theorems/90c331b1-ce8c-47e7-816f-3d2f8c2ac212
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR lemmas hypotheses example 719c75c092f9: P2 M Ground Theory Heights  Heights Numbers DVR lemmas hypotheses example 719c75c092f9
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR lemmas hypotheses example 719c75c092f9 construction uses the P2 M Ground Theory Heights  Heights Numbers DVR lemmas hypotheses example 719c75c092f9 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/IsMultiHomogIdealSpanSingleton.lean#L156-L188
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/IsMultiHomogIdealSpanSingleton.lean#L156-L188

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsCN
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_Cartier
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_IsMultiHomogIdealSpanSingleton
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

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_lemmas_hypotheses_example_719c75c092f9 :
    let S := MRing (fun _ : Unit => Fin 2) ℤ_[2]
    let ϖ : ℤ_[2] := ((2 : ℕ) : ℤ_[2])
    let H : Ideal S := Ideal.span {X ⟨(), 0⟩}
    IsModelOver (⊥ : Ideal S) 1 ∧ (X ⟨(), 0⟩ : S) ∉ (⊥ : Ideal S) ∧ (X ⟨(), 1⟩ : S) ∉ (⊥ : Ideal S) ∧
      IsVerticalDivisor (⊥ : Ideal S) ϖ 0 (C ϖ) 1 ∧
      IsMultiProjPrime H ∧ (⊥ : Ideal S) ≤ H ∧ (C ϖ : S) ∉ H ∧
      H ∈ ((⊥ : Ideal S) ⊔ Ideal.span {X ⟨(), 0⟩}).minimalPrimes := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«lemmas_hypotheses_example» := P2M_GroundTheory_Heights__Heights_NumbersDVR_lemmas_hypotheses_example_719c75c092f9
