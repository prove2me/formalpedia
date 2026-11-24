-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Model_DescendHom_pullSectionOn_comp_inv_04357edd9e0d
-- name    : P2M_GroundTheory_Heights__Heights_Model_DescendHom_pullSectionOn_comp_inv_04357edd9e0d
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:09:32.625796+00:00
-- url     : https://prove2.me/theorems/4c692c62-4ed1-4015-8761-a94e9ac9d74c
-- title:
--   P2 M Ground Theory Heights  Heights Model Descend Hom pull Section On comp inv 04357edd9e0d: P2 M Ground Theory Heights  Heights Model Descend Hom pull Section On comp inv 04357edd9e0d
-- statement:
--   The P2 M Ground Theory Heights  Heights Model Descend Hom pull Section On comp inv 04357edd9e0d construction uses the P2 M Ground Theory Heights  Heights Model Descend Hom pull Section On comp inv 04357edd9e0d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/PDescendHom.lean#L40-L51
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/PDescendHom.lean#L40-L51

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

theorem P2M_GroundTheory_Heights__Heights_Model_DescendHom_pullSectionOn_comp_inv_04357edd9e0d (f : T ⟶ Z) (h : Z ⟶ Y) (M : Y.Modules) (O : Y.Opens) (m : Γ(M, O)) :
    ((Scheme.Modules.pullbackComp f h).inv.app M).app ((f ≫ h) ⁻¹ᵁ O)
      (pullSectionOn (f ≫ h) M O m) =
        pullSectionOn f _ (h ⁻¹ᵁ O) (pullSectionOn h M O m) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Model».«DescendHom».«pullSectionOn_comp_inv» := P2M_GroundTheory_Heights__Heights_Model_DescendHom_pullSectionOn_comp_inv_04357edd9e0d
