-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Model_SectionNefGenerated_hypotheses_inhabited_6b811562c9e1
-- name    : P2M_GroundTheory_Heights__Heights_Model_SectionNefGenerated_hypotheses_inhabited_6b811562c9e1
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T03:29:19.293134+00:00
-- url     : https://prove2.me/theorems/c4688cab-8020-4c3f-bb6b-ca6fed49b01b
-- title:
--   P2 M Ground Theory Heights  Heights Model Section Nef Generated hypotheses inhabited 6b811562c9e1: P2 M Ground Theory Heights  Heights Model Section Nef Generated hypotheses inhabited 6b811562c9e1
-- statement:
--   The P2 M Ground Theory Heights  Heights Model Section Nef Generated hypotheses inhabited 6b811562c9e1 construction uses the P2 M Ground Theory Heights  Heights Model Section Nef Generated hypotheses inhabited 6b811562c9e1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/Statements.lean#L605-L627
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/Statements.lean#L605-L627

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_Objects
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_BundleObjects
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_Statements
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Model
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Opposite
noncomputable section
open NumbersDVR ReciprocityTheory.ChartRestriction.G.Geo

theorem P2M_GroundTheory_Heights__Heights_Model_SectionNefGenerated_hypotheses_inhabited_6b811562c9e1 :
    IsMultiProjPrime (⊥ : Ideal (MRing (fun _ : Unit => Fin 2) ℚ)) ∧
      ringKrullDim (MRing (fun _ : Unit => Fin 2) ℚ ⧸ (⊥ : Ideal (MRing (fun _ : Unit => Fin 2) ℚ))) =
        ((1 + Fintype.card Unit : ℕ) : WithBot ℕ∞) ∧
      ∀ W : Ideal (MRing (fun _ : Unit => Fin 2) ℚ), IsMultiProjPrime W → ⊥ ≤ W →
        ∃ f g : MRing (fun _ : Unit => Fin 2) ℚ,
          IsRegularSection (⊥ : Ideal (MRing (fun _ : Unit => Fin 2) ℚ)) (fun _ => ((1 : ℕ) : ℤ)) f g ∧
          ∃ u v : MRing (fun _ : Unit => Fin 2) ℚ, u ∉ W ∧ v ∉ W ∧ u * f - v * g ∈ (⊥ : Ideal _) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Model».«SectionNefGenerated».«hypotheses_inhabited» := P2M_GroundTheory_Heights__Heights_Model_SectionNefGenerated_hypotheses_inhabited_6b811562c9e1
