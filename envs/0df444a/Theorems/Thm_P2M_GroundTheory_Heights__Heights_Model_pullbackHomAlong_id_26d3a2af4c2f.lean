-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Model_pullbackHomAlong_id_26d3a2af4c2f
-- name    : P2M_GroundTheory_Heights__Heights_Model_pullbackHomAlong_id_26d3a2af4c2f
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T04:28:42.121345+00:00
-- url     : https://prove2.me/theorems/62eb2c54-5471-4728-bba2-4d95e700d3c8
-- title:
--   P2 M Ground Theory Heights  Heights Model pullback Hom Along id 26d3a2af4c2f: P2 M Ground Theory Heights  Heights Model pullback Hom Along id 26d3a2af4c2f
-- statement:
--   The P2 M Ground Theory Heights  Heights Model pullback Hom Along id 26d3a2af4c2f construction uses the P2 M Ground Theory Heights  Heights Model pullback Hom Along id 26d3a2af4c2f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/StatementsSpreadHom.lean#L32-L34
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/StatementsSpreadHom.lean#L32-L34

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_StatementsSpreadHom
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
open CategoryTheory AlgebraicGeometry
noncomputable section
variable {T Y Z : Scheme.{0}} {g : T ⟶ Y} {h : Y ⟶ Z} {k : T ⟶ Z}

theorem P2M_GroundTheory_Heights__Heights_Model_pullbackHomAlong_id_26d3a2af4c2f (e : g ≫ h = k) (F : Z.Modules) :
    pullbackHomAlong e (𝟙 ((Scheme.Modules.pullback h).obj F)) = 𝟙 _ := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Model».«pullbackHomAlong_id» := P2M_GroundTheory_Heights__Heights_Model_pullbackHomAlong_id_26d3a2af4c2f
