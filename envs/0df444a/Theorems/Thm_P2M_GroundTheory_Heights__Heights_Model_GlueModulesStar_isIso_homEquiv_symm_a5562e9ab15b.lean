-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Model_GlueModulesStar_isIso_homEquiv_symm_a5562e9ab15b
-- name    : P2M_GroundTheory_Heights__Heights_Model_GlueModulesStar_isIso_homEquiv_symm_a5562e9ab15b
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T04:25:54.825704+00:00
-- url     : https://prove2.me/theorems/5c68e4fa-f83d-45e4-8c4e-9df8356e805f
-- title:
--   P2 M Ground Theory Heights  Heights Model Glue Modules Star is Iso hom Equiv symm a5562e9ab15b: P2 M Ground Theory Heights  Heights Model Glue Modules Star is Iso hom Equiv symm a5562e9ab15b
-- statement:
--   The P2 M Ground Theory Heights  Heights Model Glue Modules Star is Iso hom Equiv symm a5562e9ab15b construction uses the P2 M Ground Theory Heights  Heights Model Glue Modules Star is Iso hom Equiv symm a5562e9ab15b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/PGlueModulesStar.lean#L94-L108
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/PGlueModulesStar.lean#L94-L108

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

theorem P2M_GroundTheory_Heights__Heights_Model_GlueModulesStar_isIso_homEquiv_symm_a5562e9ab15b {Y Z : Scheme.{u}} (f : Y ⟶ Z) [IsOpenImmersion f] {E : Z.Modules}
    {M : Y.Modules} (φ : E ⟶ (pushforward f).obj M) (h : ∀ O : Y.Opens, IsIso (φ.app (f ''ᵁ O))) :
    IsIso (((pullbackPushforwardAdjunction f).homEquiv _ _).symm φ) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Model».«GlueModulesStar».«isIso_homEquiv_symm» := P2M_GroundTheory_Heights__Heights_Model_GlueModulesStar_isIso_homEquiv_symm_a5562e9ab15b
