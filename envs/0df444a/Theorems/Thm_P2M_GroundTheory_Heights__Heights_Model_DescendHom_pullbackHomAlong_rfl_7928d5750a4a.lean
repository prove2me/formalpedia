-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Model_DescendHom_pullbackHomAlong_rfl_7928d5750a4a
-- name    : P2M_GroundTheory_Heights__Heights_Model_DescendHom_pullbackHomAlong_rfl_7928d5750a4a
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T03:50:08.862504+00:00
-- url     : https://prove2.me/theorems/ae55d5df-2994-4857-80d5-bde31567095c
-- title:
--   P2 M Ground Theory Heights  Heights Model Descend Hom pullback Hom Along rfl 7928d5750a4a: P2 M Ground Theory Heights  Heights Model Descend Hom pullback Hom Along rfl 7928d5750a4a
-- statement:
--   The P2 M Ground Theory Heights  Heights Model Descend Hom pullback Hom Along rfl 7928d5750a4a construction uses the P2 M Ground Theory Heights  Heights Model Descend Hom pullback Hom Along rfl 7928d5750a4a property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/PDescendHom.lean#L88-L92
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/PDescendHom.lean#L88-L92

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_StatementsDescendHom
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_PClearDenominators
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_PDescendHom
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
open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite
noncomputable section
open GroundTheory.Heights₂.Heights.Model.DescendHom
variable {T Y Z : Scheme.{0}}

theorem P2M_GroundTheory_Heights__Heights_Model_DescendHom_pullbackHomAlong_rfl_7928d5750a4a (ι : Z ⟶ Y) (g' : T ⟶ Z) {F G : Y.Modules}
    (ψ : (Scheme.Modules.pullback ι).obj F ⟶ (Scheme.Modules.pullback ι).obj G) :
    pullbackHomAlong (rfl : g' ≫ ι = g' ≫ ι) ψ = (Scheme.Modules.pullbackComp g' ι).inv.app F ≫
      (Scheme.Modules.pullback g').map ψ ≫ (Scheme.Modules.pullbackComp g' ι).hom.app G := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Model».«DescendHom».«pullbackHomAlong_rfl» := P2M_GroundTheory_Heights__Heights_Model_DescendHom_pullbackHomAlong_rfl_7928d5750a4a
