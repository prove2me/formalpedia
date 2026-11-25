-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_pairNum_pushExpansion_bef8f5d6e996
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_pairNum_pushExpansion_bef8f5d6e996
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:09:19.492975+00:00
-- url     : https://prove2.me/theorems/122023c8-8d82-4940-9e4c-d028dd877ced
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR pair Num push Expansion bef8f5d6e996: P2 M Ground Theory Heights  Heights Numbers DVR pair Num push Expansion bef8f5d6e996
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR pair Num push Expansion bef8f5d6e996 construction uses the P2 M Ground Theory Heights  Heights Numbers DVR pair Num push Expansion bef8f5d6e996 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PFlagIndependenceAlgebra.lean#L126-L162
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PFlagIndependenceAlgebra.lean#L126-L162

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsFlagIndependence
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PFlagIndependenceAlgebra
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
variable {K : Type*} [Fintype K] [DecidableEq K] {ι : K → Type*} [∀ k, Fintype (ι k)]
  {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_pairNum_pushExpansion_bef8f5d6e996 {n n' : ℕ} (σ : Fin n → Fin n') (P : Ideal (MRing ι O))
    (x x' : Fin n' → K → ℤ) (f g : Fin n' → MRing ι O)
    (Gs : Fin n → MvPolynomial (Fin n ⊕ Fin n) ℤ) (Q : List (K → ℤ)) :
    pairNum P x x' f g (pushExpansion σ Gs) Q =
      pairNum P (x ∘ σ) (x' ∘ σ) (f ∘ σ) (g ∘ σ) Gs Q := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«pairNum_pushExpansion» := P2M_GroundTheory_Heights__Heights_NumbersDVR_pairNum_pushExpansion_bef8f5d6e996
