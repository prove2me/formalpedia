-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Model_DescendHom_pullSectionOn_comp_hom_52f3a44a95f5
-- name    : P2M_GroundTheory_Heights__Heights_Model_DescendHom_pullSectionOn_comp_hom_52f3a44a95f5
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T03:50:10.323312+00:00
-- url     : https://prove2.me/theorems/84e6beea-3687-4c89-b78a-5b3bd0c8270b
-- title:
--   P2 M Ground Theory Heights  Heights Model Descend Hom pull Section On comp hom 52f3a44a95f5: P2 M Ground Theory Heights  Heights Model Descend Hom pull Section On comp hom 52f3a44a95f5
-- statement:
--   The P2 M Ground Theory Heights  Heights Model Descend Hom pull Section On comp hom 52f3a44a95f5 construction uses the P2 M Ground Theory Heights  Heights Model Descend Hom pull Section On comp hom 52f3a44a95f5 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/PDescendHom.lean#L53-L58
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/PDescendHom.lean#L53-L58

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

theorem P2M_GroundTheory_Heights__Heights_Model_DescendHom_pullSectionOn_comp_hom_52f3a44a95f5 (f : T ⟶ Z) (h : Z ⟶ Y) (M : Y.Modules) (O : Y.Opens) (m : Γ(M, O)) :
    ((Scheme.Modules.pullbackComp f h).hom.app M).app ((f ≫ h) ⁻¹ᵁ O)
      (pullSectionOn f _ (h ⁻¹ᵁ O) (pullSectionOn h M O m)) = pullSectionOn (f ≫ h) M O m := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Model».«DescendHom».«pullSectionOn_comp_hom» := P2M_GroundTheory_Heights__Heights_Model_DescendHom_pullSectionOn_comp_hom_52f3a44a95f5
