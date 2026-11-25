-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_pairNumHom_apply_88787fdf61cc
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_pairNumHom_apply_88787fdf61cc
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T04:11:58.972198+00:00
-- url     : https://prove2.me/theorems/2d0e9137-ec60-46b9-af29-fbd743669fd9
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR pair Num Hom apply 88787fdf61cc: P2 M Ground Theory Heights  Heights Numbers DVR pair Num Hom apply 88787fdf61cc
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR pair Num Hom apply 88787fdf61cc construction uses the P2 M Ground Theory Heights  Heights Numbers DVR pair Num Hom apply 88787fdf61cc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PFlagIndependenceAlgebra.lean#L118-L120
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PFlagIndependenceAlgebra.lean#L118-L120

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

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_pairNumHom_apply_88787fdf61cc {n : ℕ} (P : Ideal (MRing ι O)) (x x' : Fin n → K → ℤ)
    (f g : Fin n → MRing ι O) (Q : List (K → ℤ)) (Gs : Fin n → MvPolynomial (Fin n ⊕ Fin n) ℤ) :
    pairNumHom P x x' f g Q Gs = pairNum P x x' f g Gs Q := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«pairNumHom_apply» := P2M_GroundTheory_Heights__Heights_NumbersDVR_pairNumHom_apply_88787fdf61cc
