-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Model_BundlesAgree_germ_homOfGeneric_app_ae35dc9a743d
-- name    : P2M_GroundTheory_Heights__Heights_Model_BundlesAgree_germ_homOfGeneric_app_ae35dc9a743d
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T03:50:20.153672+00:00
-- url     : https://prove2.me/theorems/9f47f6ea-2d6f-520a-a88c-330b451bb8c4
-- title:
--   P2 M Ground Theory Heights  Heights Model Bundles Agree germ hom Of Generic app ae35dc9a743d: P2 M Ground Theory Heights  Heights Model Bundles Agree germ hom Of Generic app ae35dc9a743d
-- statement:
--   The P2 M Ground Theory Heights  Heights Model Bundles Agree germ hom Of Generic app ae35dc9a743d construction uses the P2 M Ground Theory Heights  Heights Model Bundles Agree germ hom Of Generic app ae35dc9a743d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/PBundlesAgree.lean#L104-L107
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/PBundlesAgree.lean#L104-L107

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_StatementsGenericGerm
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_StatementsHeightOneSections
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_PBundlesAgree
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
open GroundTheory.Heights₂.Heights.Model.BundlesAgree
variable {X : Scheme.{0}} [IsIntegral X]
variable (E E' : X.Modules)
  (φ : E.presheaf.stalk (genericPoint X) →ₗ[X.presheaf.stalk (genericPoint X)]
    E'.presheaf.stalk (genericPoint X))
  (hex : ∀ (U : X.Opens) (hU : genericPoint X ∈ U) (s : Γ(E, U)), ∃ t : Γ(E', U),
    E'.presheaf.germ U (genericPoint X) hU t = φ (E.presheaf.germ U (genericPoint X) hU s))
  (hE' : ∀ (U : X.Opens) (hU : genericPoint X ∈ U),
      Function.Injective (E'.presheaf.germ U (genericPoint X) hU))
include hE'

theorem P2M_GroundTheory_Heights__Heights_Model_BundlesAgree_germ_homOfGeneric_app_ae35dc9a743d (U : X.Opens) (hU : genericPoint X ∈ U) (s : Γ(E, U)) :
    E'.presheaf.germ U (genericPoint X) hU ((homOfGeneric E E' φ hex hE').app U s) =
      φ (E.presheaf.germ U (genericPoint X) hU s) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Model».«BundlesAgree».«germ_homOfGeneric_app» := P2M_GroundTheory_Heights__Heights_Model_BundlesAgree_germ_homOfGeneric_app_ae35dc9a743d
