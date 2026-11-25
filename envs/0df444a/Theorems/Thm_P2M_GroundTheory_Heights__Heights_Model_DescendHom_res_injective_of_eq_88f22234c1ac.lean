-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Model_DescendHom_res_injective_of_eq_88f22234c1ac
-- name    : P2M_GroundTheory_Heights__Heights_Model_DescendHom_res_injective_of_eq_88f22234c1ac
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T03:49:56.619272+00:00
-- url     : https://prove2.me/theorems/fa0a51b1-352f-4e6c-a760-4038faa01a13
-- title:
--   P2 M Ground Theory Heights  Heights Model Descend Hom res injective of eq 88f22234c1ac: P2 M Ground Theory Heights  Heights Model Descend Hom res injective of eq 88f22234c1ac
-- statement:
--   The P2 M Ground Theory Heights  Heights Model Descend Hom res injective of eq 88f22234c1ac construction uses the P2 M Ground Theory Heights  Heights Model Descend Hom res injective of eq 88f22234c1ac property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/PDescendHom.lean#L24-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/PDescendHom.lean#L24-L28

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

theorem P2M_GroundTheory_Heights__Heights_Model_DescendHom_res_injective_of_eq_88f22234c1ac (M : Y.Modules) {U V : Y.Opens} (h : U = V) (i : U ⟶ V) :
    Function.Injective (M.presheaf.map i.op) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Model».«DescendHom».«res_injective_of_eq» := P2M_GroundTheory_Heights__Heights_Model_DescendHom_res_injective_of_eq_88f22234c1ac
