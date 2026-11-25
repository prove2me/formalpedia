-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Model_BundlesAgree_hom_ext_of_germ_e9a54a5bbb2d
-- name    : P2M_GroundTheory_Heights__Heights_Model_BundlesAgree_hom_ext_of_germ_e9a54a5bbb2d
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T03:49:24.937463+00:00
-- url     : https://prove2.me/theorems/4cd2871f-80c6-497c-a7b2-4e8bcc76e6d9
-- title:
--   P2 M Ground Theory Heights  Heights Model Bundles Agree hom ext of germ e9a54a5bbb2d: P2 M Ground Theory Heights  Heights Model Bundles Agree hom ext of germ e9a54a5bbb2d
-- statement:
--   The P2 M Ground Theory Heights  Heights Model Bundles Agree hom ext of germ e9a54a5bbb2d construction uses the P2 M Ground Theory Heights  Heights Model Bundles Agree hom ext of germ e9a54a5bbb2d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/PBundlesAgree.lean#L111-L117
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/PBundlesAgree.lean#L111-L117

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

theorem P2M_GroundTheory_Heights__Heights_Model_BundlesAgree_hom_ext_of_germ_e9a54a5bbb2d {f g : E ⟶ E'}
    (h : ∀ (U : X.Opens) (hU : genericPoint X ∈ U) (s : Γ(E, U)),
      E'.presheaf.germ U (genericPoint X) hU (f.app U s) =
        E'.presheaf.germ U (genericPoint X) hU (g.app U s)) : f = g := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Model».«BundlesAgree».«hom_ext_of_germ» := P2M_GroundTheory_Heights__Heights_Model_BundlesAgree_hom_ext_of_germ_e9a54a5bbb2d
