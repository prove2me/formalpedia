-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Model_IsoGlueTwo_homEquiv_pullbackIsoAlong_d3b70a0e6bc0
-- name    : P2M_GroundTheory_Heights__Heights_Model_IsoGlueTwo_homEquiv_pullbackIsoAlong_d3b70a0e6bc0
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T03:43:51.560237+00:00
-- url     : https://prove2.me/theorems/26f13e1c-05f7-5b0e-aa8a-4e145221da6a
-- title:
--   P2 M Ground Theory Heights  Heights Model Iso Glue Two hom Equiv pullback Iso Along d3b70a0e6bc0: P2 M Ground Theory Heights  Heights Model Iso Glue Two hom Equiv pullback Iso Along d3b70a0e6bc0
-- statement:
--   The P2 M Ground Theory Heights  Heights Model Iso Glue Two hom Equiv pullback Iso Along d3b70a0e6bc0 construction uses the P2 M Ground Theory Heights  Heights Model Iso Glue Two hom Equiv pullback Iso Along d3b70a0e6bc0 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/PIsoGlueTwo.lean#L78-L90
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/PIsoGlueTwo.lean#L78-L90

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

theorem P2M_GroundTheory_Heights__Heights_Model_IsoGlueTwo_homEquiv_pullbackIsoAlong_d3b70a0e6bc0 (g : T ⟶ Z₁) (f : Z₁ ⟶ X) {k : T ⟶ X} (e : g ≫ f = k)
    {A B : X.Modules}
    (φ : (Scheme.Modules.pullback f).obj A ≅ (Scheme.Modules.pullback f).obj B) :
    (pullbackPushforwardAdjunction k).homEquiv _ _ (pullbackIsoAlong e φ).hom =
      (pullbackPushforwardAdjunction f).homEquiv _ _ φ.hom ≫ restrictOverlap g f e B := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Model».«IsoGlueTwo».«homEquiv_pullbackIsoAlong» := P2M_GroundTheory_Heights__Heights_Model_IsoGlueTwo_homEquiv_pullbackIsoAlong_d3b70a0e6bc0
