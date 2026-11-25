-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Model_IsoGlueTwo_exists_hom_4266bc55ec24
-- name    : P2M_GroundTheory_Heights__Heights_Model_IsoGlueTwo_exists_hom_4266bc55ec24
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T03:30:28.684934+00:00
-- url     : https://prove2.me/theorems/ec241510-0a25-42a0-a0c7-605690653c2f
-- title:
--   P2 M Ground Theory Heights  Heights Model Iso Glue Two exists hom 4266bc55ec24: P2 M Ground Theory Heights  Heights Model Iso Glue Two exists hom 4266bc55ec24
-- statement:
--   The P2 M Ground Theory Heights  Heights Model Iso Glue Two exists hom 4266bc55ec24 construction uses the P2 M Ground Theory Heights  Heights Model Iso Glue Two exists hom 4266bc55ec24 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/PIsoGlueTwo.lean#L181-L195
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/PIsoGlueTwo.lean#L181-L195

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_StatementsIsoGlueTwo
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_PGlueModulesStar
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_PIsoGlueTwo
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
open GroundTheory.Heights₂.Heights.Model.IsoGlueTwo
open Scheme.Modules GlueModulesStar
variable {X Z₁ Z₂ T : Scheme.{0}}
variable (f₁ : Z₁ ⟶ X) (f₂ : Z₂ ⟶ X) [IsOpenImmersion f₁] [IsOpenImmersion f₂]
  (g₁ : T ⟶ Z₁) (g₂ : T ⟶ Z₂) [IsOpenImmersion g₁] [IsOpenImmersion g₂] {k : T ⟶ X}
  (e₁ : g₁ ≫ f₁ = k) (e₂ : g₂ ≫ f₂ = k)

theorem P2M_GroundTheory_Heights__Heights_Model_IsoGlueTwo_exists_hom_4266bc55ec24 (hcov : ⊤ ≤ f₁.opensRange ⊔ f₂.opensRange)
    (h₁₂ : ∀ O : X.Opens, O ≤ f₁.opensRange → f₂ ⁻¹ᵁ O ≤ g₂.opensRange)
    (h₂₁ : ∀ O : X.Opens, O ≤ f₂.opensRange → f₁ ⁻¹ᵁ O ≤ g₁.opensRange) {A B : X.Modules}
    (φ₁ : (Scheme.Modules.pullback f₁).obj A ⟶ (Scheme.Modules.pullback f₁).obj B)
    (φ₂ : (Scheme.Modules.pullback f₂).obj A ⟶ (Scheme.Modules.pullback f₂).obj B)
    (h : (pullbackPushforwardAdjunction f₁).homEquiv _ _ φ₁ ≫ restrictOverlap g₁ f₁ e₁ B =
      (pullbackPushforwardAdjunction f₂).homEquiv _ _ φ₂ ≫ restrictOverlap g₂ f₂ e₂ B) :
    ∃ α : A ⟶ B, (Scheme.Modules.pullback f₁).map α = φ₁ ∧
      (Scheme.Modules.pullback f₂).map α = φ₂ := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Model».«IsoGlueTwo».«exists_hom» := P2M_GroundTheory_Heights__Heights_Model_IsoGlueTwo_exists_hom_4266bc55ec24
