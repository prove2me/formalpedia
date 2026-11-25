-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_koszul_homogeneous_3d5b5d9ab1aa
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_koszul_homogeneous_3d5b5d9ab1aa
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T08:08:19.956261+00:00
-- url     : https://prove2.me/theorems/153ac074-1f1b-5bc3-8b88-6c8b2f42bf22
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR koszul homogeneous 3d5b5d9ab1aa: P2 M Ground Theory Heights  Heights Numbers DVR koszul homogeneous 3d5b5d9ab1aa
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR koszul homogeneous 3d5b5d9ab1aa construction uses the P2 M Ground Theory Heights  Heights Numbers DVR koszul homogeneous 3d5b5d9ab1aa property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PPairNumberExpansionKoszul.lean#L168-L193
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PPairNumberExpansionKoszul.lean#L168-L193

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PFlagIndependenceAlgebra
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PMixedDiffLinear
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_OfSteps
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PPairNumberExpansionKoszul
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
variable {n : ℕ}

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_koszul_homogeneous_3d5b5d9ab1aa {m : ℕ} (G : Fin n → MvPolynomial (Fin n ⊕ Fin n) ℤ)
    (hG : ∀ i, (G i).IsHomogeneous (m - 1)) (hrel : ∑ i, pairDiff i * G i = 0) :
    ∃ K : Fin n → Fin n → MvPolynomial (Fin n ⊕ Fin n) ℤ,
      (∀ i j, K i j = -K j i) ∧ (∀ i j, (K i j).IsHomogeneous (m - 2)) ∧
      (m - 1 = 0 → ∀ i j, K i j = 0) ∧ ∀ i, G i = ∑ j, pairDiff j * K i j := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«koszul_homogeneous» := P2M_GroundTheory_Heights__Heights_NumbersDVR_koszul_homogeneous_3d5b5d9ab1aa
