-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Model_DescendHom_pullSectionOn_naturality_945819a8bd40
-- name    : P2M_GroundTheory_Heights__Heights_Model_DescendHom_pullSectionOn_naturality_945819a8bd40
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T03:50:59.212851+00:00
-- url     : https://prove2.me/theorems/9988b8b3-f7ee-5169-b1fe-c93aea5590ed
-- title:
--   P2 M Ground Theory Heights  Heights Model Descend Hom pull Section On naturality 945819a8bd40: P2 M Ground Theory Heights  Heights Model Descend Hom pull Section On naturality 945819a8bd40
-- statement:
--   The P2 M Ground Theory Heights  Heights Model Descend Hom pull Section On naturality 945819a8bd40 construction uses the P2 M Ground Theory Heights  Heights Model Descend Hom pull Section On naturality 945819a8bd40 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/PDescendHom.lean#L30-L38
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/PDescendHom.lean#L30-L38

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

theorem P2M_GroundTheory_Heights__Heights_Model_DescendHom_pullSectionOn_naturality_945819a8bd40 (g : T ⟶ Y) {M N : Y.Modules} (χ : M ⟶ N) (V : Y.Opens)
    (m : Γ(M, V)) :
    ((Scheme.Modules.pullback g).map χ).app (g ⁻¹ᵁ V) (pullSectionOn g M V m) =
      pullSectionOn g N V (χ.app V m) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Model».«DescendHom».«pullSectionOn_naturality» := P2M_GroundTheory_Heights__Heights_Model_DescendHom_pullSectionOn_naturality_945819a8bd40
