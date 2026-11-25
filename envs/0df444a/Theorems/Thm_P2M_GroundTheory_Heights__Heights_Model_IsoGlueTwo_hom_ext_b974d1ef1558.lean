-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Model_IsoGlueTwo_hom_ext_b974d1ef1558
-- name    : P2M_GroundTheory_Heights__Heights_Model_IsoGlueTwo_hom_ext_b974d1ef1558
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T03:29:24.137432+00:00
-- url     : https://prove2.me/theorems/5c384d1a-21a2-430a-a11d-d3e2b178d4c7
-- title:
--   P2 M Ground Theory Heights  Heights Model Iso Glue Two hom ext b974d1ef1558: P2 M Ground Theory Heights  Heights Model Iso Glue Two hom ext b974d1ef1558
-- statement:
--   The P2 M Ground Theory Heights  Heights Model Iso Glue Two hom ext b974d1ef1558 construction uses the P2 M Ground Theory Heights  Heights Model Iso Glue Two hom ext b974d1ef1558 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/PIsoGlueTwo.lean#L172-L179
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/PIsoGlueTwo.lean#L172-L179

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
include e₁ e₂

theorem P2M_GroundTheory_Heights__Heights_Model_IsoGlueTwo_hom_ext_b974d1ef1558 (hcov : ⊤ ≤ f₁.opensRange ⊔ f₂.opensRange)
    (h₁₂ : ∀ O : X.Opens, O ≤ f₁.opensRange → f₂ ⁻¹ᵁ O ≤ g₂.opensRange)
    (h₂₁ : ∀ O : X.Opens, O ≤ f₂.opensRange → f₁ ⁻¹ᵁ O ≤ g₁.opensRange) {A B : X.Modules} (α β : A ⟶ B)
    (h₁ : (Scheme.Modules.pullback f₁).map α = (Scheme.Modules.pullback f₁).map β)
    (h₂ : (Scheme.Modules.pullback f₂).map α = (Scheme.Modules.pullback f₂).map β) : α = β := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Model».«IsoGlueTwo».«hom_ext» := P2M_GroundTheory_Heights__Heights_Model_IsoGlueTwo_hom_ext_b974d1ef1558
