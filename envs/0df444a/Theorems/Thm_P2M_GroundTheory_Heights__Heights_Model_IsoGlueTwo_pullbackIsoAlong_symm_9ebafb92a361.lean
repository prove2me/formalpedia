-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Model_IsoGlueTwo_pullbackIsoAlong_symm_9ebafb92a361
-- name    : P2M_GroundTheory_Heights__Heights_Model_IsoGlueTwo_pullbackIsoAlong_symm_9ebafb92a361
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T03:33:24.302313+00:00
-- url     : https://prove2.me/theorems/ea23dfad-a13e-46ad-8cfa-9e4cfda9817f
-- title:
--   P2 M Ground Theory Heights  Heights Model Iso Glue Two pullback Iso Along symm 9ebafb92a361: P2 M Ground Theory Heights  Heights Model Iso Glue Two pullback Iso Along symm 9ebafb92a361
-- statement:
--   The P2 M Ground Theory Heights  Heights Model Iso Glue Two pullback Iso Along symm 9ebafb92a361 construction uses the P2 M Ground Theory Heights  Heights Model Iso Glue Two pullback Iso Along symm 9ebafb92a361 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/PIsoGlueTwo.lean#L92-L98
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/PIsoGlueTwo.lean#L92-L98

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

theorem P2M_GroundTheory_Heights__Heights_Model_IsoGlueTwo_pullbackIsoAlong_symm_9ebafb92a361 (g : T ⟶ Z₁) (f : Z₁ ⟶ X) {k : T ⟶ X} (e : g ≫ f = k)
    {A B : X.Modules}
    (φ : (Scheme.Modules.pullback f).obj A ≅ (Scheme.Modules.pullback f).obj B) :
    pullbackIsoAlong e φ.symm = (pullbackIsoAlong e φ).symm := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Model».«IsoGlueTwo».«pullbackIsoAlong_symm» := P2M_GroundTheory_Heights__Heights_Model_IsoGlueTwo_pullbackIsoAlong_symm_9ebafb92a361
