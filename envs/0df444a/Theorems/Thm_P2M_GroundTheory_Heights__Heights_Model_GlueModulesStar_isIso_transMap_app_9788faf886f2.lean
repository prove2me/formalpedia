-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Model_GlueModulesStar_isIso_transMap_app_9788faf886f2
-- name    : P2M_GroundTheory_Heights__Heights_Model_GlueModulesStar_isIso_transMap_app_9788faf886f2
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:34:53.85085+00:00
-- url     : https://prove2.me/theorems/fb548b04-23d5-4960-8e4f-c9792ba74017
-- title:
--   P2 M Ground Theory Heights  Heights Model Glue Modules Star is Iso trans Map app 9788faf886f2: P2 M Ground Theory Heights  Heights Model Glue Modules Star is Iso trans Map app 9788faf886f2
-- statement:
--   The P2 M Ground Theory Heights  Heights Model Glue Modules Star is Iso trans Map app 9788faf886f2 construction uses the P2 M Ground Theory Heights  Heights Model Glue Modules Star is Iso trans Map app 9788faf886f2 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/PGlueModulesStar.lean#L121-L129
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/PGlueModulesStar.lean#L121-L129

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
set_option backward.isDefEq.respectTransparency false
open Scheme.Modules

theorem P2M_GroundTheory_Heights__Heights_Model_GlueModulesStar_isIso_transMap_app_9788faf886f2 {A B Z : Scheme.{u}} (f : A ⟶ B) [IsOpenImmersion f] (h : B ⟶ Z)
    {k : A ⟶ Z} (e : f ≫ h = k) {M : B.Modules} {N : A.Modules} (χ : (Scheme.Modules.pullback f).obj M ⟶ N)
    [IsIso χ] (O : Z.Opens) (hO : h ⁻¹ᵁ O ≤ f.opensRange) :
    IsIso ((transMap f h e χ).app O) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Model».«GlueModulesStar».«isIso_transMap_app» := P2M_GroundTheory_Heights__Heights_Model_GlueModulesStar_isIso_transMap_app_9788faf886f2
