-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Model_BundlesAgree_germ_app_eq_stalk_95beff67d4e5
-- name    : P2M_GroundTheory_Heights__Heights_Model_BundlesAgree_germ_app_eq_stalk_95beff67d4e5
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T03:50:07.91059+00:00
-- url     : https://prove2.me/theorems/682363b9-d9bf-5930-b93a-d7ac5cbd3682
-- title:
--   P2 M Ground Theory Heights  Heights Model Bundles Agree germ app eq stalk 95beff67d4e5: P2 M Ground Theory Heights  Heights Model Bundles Agree germ app eq stalk 95beff67d4e5
-- statement:
--   The P2 M Ground Theory Heights  Heights Model Bundles Agree germ app eq stalk 95beff67d4e5 construction uses the P2 M Ground Theory Heights  Heights Model Bundles Agree germ app eq stalk 95beff67d4e5 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/PBundlesAgree.lean#L121-L127
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/PBundlesAgree.lean#L121-L127

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
omit [IsIntegral X]

theorem P2M_GroundTheory_Heights__Heights_Model_BundlesAgree_germ_app_eq_stalk_95beff67d4e5 (f : E ⟶ E') (U : X.Opens) (x : X) (hU : x ∈ U) (s : Γ(E, U)) :
    E'.presheaf.germ U x hU (f.app U s) =
      ((TopCat.Presheaf.stalkFunctor Ab x).map (Scheme.Modules.Hom.mapPresheaf f)).hom
        (E.presheaf.germ U x hU s) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Model».«BundlesAgree».«germ_app_eq_stalk» := P2M_GroundTheory_Heights__Heights_Model_BundlesAgree_germ_app_eq_stalk_95beff67d4e5
