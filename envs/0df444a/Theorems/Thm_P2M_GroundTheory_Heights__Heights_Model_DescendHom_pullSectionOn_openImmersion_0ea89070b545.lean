-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Model_DescendHom_pullSectionOn_openImmersion_0ea89070b545
-- name    : P2M_GroundTheory_Heights__Heights_Model_DescendHom_pullSectionOn_openImmersion_0ea89070b545
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T03:51:04.374192+00:00
-- url     : https://prove2.me/theorems/bc134c11-c005-53a4-98b2-ccbbc06a0881
-- title:
--   P2 M Ground Theory Heights  Heights Model Descend Hom pull Section On open Immersion 0ea89070b545: P2 M Ground Theory Heights  Heights Model Descend Hom pull Section On open Immersion 0ea89070b545
-- statement:
--   The P2 M Ground Theory Heights  Heights Model Descend Hom pull Section On open Immersion 0ea89070b545 construction uses the P2 M Ground Theory Heights  Heights Model Descend Hom pull Section On open Immersion 0ea89070b545 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/PDescendHom.lean#L60-L67
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/PDescendHom.lean#L60-L67

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

theorem P2M_GroundTheory_Heights__Heights_Model_DescendHom_pullSectionOn_openImmersion_0ea89070b545 (ι : Z ⟶ Y) [IsOpenImmersion ι] (M : Y.Modules) (O : Y.Opens)
    (m : Γ(M, O)) :
    pullSectionOn ι M O m = ((Scheme.Modules.restrictFunctorIsoPullback ι).hom.app M).app (ι ⁻¹ᵁ O)
      ((M.restrictAppIso ι (ι ⁻¹ᵁ O)).inv (M.presheaf.map (homOfLE (ι.image_preimage_le O)).op m)) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Model».«DescendHom».«pullSectionOn_openImmersion» := P2M_GroundTheory_Heights__Heights_Model_DescendHom_pullSectionOn_openImmersion_0ea89070b545
