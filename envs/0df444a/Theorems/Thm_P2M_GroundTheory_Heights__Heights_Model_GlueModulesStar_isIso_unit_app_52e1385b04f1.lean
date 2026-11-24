-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Model_GlueModulesStar_isIso_unit_app_52e1385b04f1
-- name    : P2M_GroundTheory_Heights__Heights_Model_GlueModulesStar_isIso_unit_app_52e1385b04f1
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:26:06.604453+00:00
-- url     : https://prove2.me/theorems/c572f80c-4a81-493a-bebd-c8710e319334
-- title:
--   P2 M Ground Theory Heights  Heights Model Glue Modules Star is Iso unit app 52e1385b04f1: P2 M Ground Theory Heights  Heights Model Glue Modules Star is Iso unit app 52e1385b04f1
-- statement:
--   The P2 M Ground Theory Heights  Heights Model Glue Modules Star is Iso unit app 52e1385b04f1 construction uses the P2 M Ground Theory Heights  Heights Model Glue Modules Star is Iso unit app 52e1385b04f1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/PGlueModulesStar.lean#L78-L90
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/PGlueModulesStar.lean#L78-L90

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

theorem P2M_GroundTheory_Heights__Heights_Model_GlueModulesStar_isIso_unit_app_52e1385b04f1 {Y Z : Scheme.{u}} (f : Y ⟶ Z) [IsOpenImmersion f] (M : Z.Modules)
    (O : Z.Opens) (hO : O ≤ f.opensRange) :
    IsIso (((pullbackPushforwardAdjunction f).unit.app M).app O) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Model».«GlueModulesStar».«isIso_unit_app» := P2M_GroundTheory_Heights__Heights_Model_GlueModulesStar_isIso_unit_app_52e1385b04f1
