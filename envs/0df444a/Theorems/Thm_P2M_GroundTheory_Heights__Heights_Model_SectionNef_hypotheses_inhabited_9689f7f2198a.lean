-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Model_SectionNef_hypotheses_inhabited_9689f7f2198a
-- name    : P2M_GroundTheory_Heights__Heights_Model_SectionNef_hypotheses_inhabited_9689f7f2198a
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T03:29:42.063397+00:00
-- url     : https://prove2.me/theorems/c274b9d6-e415-4c7e-a169-f7ac3d001f7e
-- title:
--   P2 M Ground Theory Heights  Heights Model Section Nef hypotheses inhabited 9689f7f2198a: P2 M Ground Theory Heights  Heights Model Section Nef hypotheses inhabited 9689f7f2198a
-- statement:
--   The P2 M Ground Theory Heights  Heights Model Section Nef hypotheses inhabited 9689f7f2198a construction uses the P2 M Ground Theory Heights  Heights Model Section Nef hypotheses inhabited 9689f7f2198a property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/Statements.lean#L594-L603
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/Statements.lean#L594-L603

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

theorem P2M_GroundTheory_Heights__Heights_Model_SectionNef_hypotheses_inhabited_9689f7f2198a :
    IsMultiProjPrime (⊥ : Ideal (MRing (fun _ : Unit => Fin 2) ℚ)) ∧
      ringKrullDim (MRing (fun _ : Unit => Fin 2) ℚ ⧸ (⊥ : Ideal (MRing (fun _ : Unit => Fin 2) ℚ))) =
        ((1 + Fintype.card Unit : ℕ) : WithBot ℕ∞) ∧
      IsRegularSection (⊥ : Ideal (MRing (fun _ : Unit => Fin 2) ℚ)) (fun _ => ((1 : ℕ) : ℤ))
        (MvPolynomial.X ⟨(), 0⟩) 1 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Model».«SectionNef».«hypotheses_inhabited» := P2M_GroundTheory_Heights__Heights_Model_SectionNef_hypotheses_inhabited_9689f7f2198a
