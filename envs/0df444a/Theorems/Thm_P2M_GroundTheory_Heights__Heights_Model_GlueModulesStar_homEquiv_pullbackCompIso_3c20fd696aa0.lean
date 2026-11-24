-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Model_GlueModulesStar_homEquiv_pullbackCompIso_3c20fd696aa0
-- name    : P2M_GroundTheory_Heights__Heights_Model_GlueModulesStar_homEquiv_pullbackCompIso_3c20fd696aa0
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:32:13.315934+00:00
-- url     : https://prove2.me/theorems/8dbd13cc-a052-4ef6-aafb-a80b19a1ffbb
-- title:
--   P2 M Ground Theory Heights  Heights Model Glue Modules Star hom Equiv pullback Comp Iso 3c20fd696aa0: P2 M Ground Theory Heights  Heights Model Glue Modules Star hom Equiv pullback Comp Iso 3c20fd696a
-- statement:
--   The P2 M Ground Theory Heights  Heights Model Glue Modules Star hom Equiv pullback Comp Iso 3c20fd696aa0 construction uses the P2 M Ground Theory Heights  Heights Model Glue Modules Star hom Equiv pullback Comp Iso 3c20fd696aa0 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/PGlueModulesStar.lean#L133-L159
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/PGlueModulesStar.lean#L133-L159

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_StatementsGlue
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_PGlueModulesStar
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
open GroundTheory.Heights₂.Heights.Model.GlueModulesStar
universe u
open Scheme.Modules

theorem P2M_GroundTheory_Heights__Heights_Model_GlueModulesStar_homEquiv_pullbackCompIso_3c20fd696aa0 {T Y Z : Scheme.{u}} {g : T ⟶ Y} {h : Y ⟶ Z} {k : T ⟶ Z}
    (e : g ≫ h = k) {E : Z.Modules} {F : Y.Modules} (γ : (Scheme.Modules.pullback h).obj E ≅ F) {M : T.Modules}
    (χ : (Scheme.Modules.pullback g).obj F ⟶ M) :
    (pullbackPushforwardAdjunction k).homEquiv _ _ ((pullbackCompIso e γ).hom ≫ χ) =
      (pullbackPushforwardAdjunction h).homEquiv _ _ γ.hom ≫ transMap g h e χ := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Model».«GlueModulesStar».«homEquiv_pullbackCompIso» := P2M_GroundTheory_Heights__Heights_Model_GlueModulesStar_homEquiv_pullbackCompIso_3c20fd696aa0
