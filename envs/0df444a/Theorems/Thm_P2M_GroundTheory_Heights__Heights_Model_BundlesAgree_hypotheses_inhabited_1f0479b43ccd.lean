-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Model_BundlesAgree_hypotheses_inhabited_1f0479b43ccd
-- name    : P2M_GroundTheory_Heights__Heights_Model_BundlesAgree_hypotheses_inhabited_1f0479b43ccd
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T03:49:08.19624+00:00
-- url     : https://prove2.me/theorems/65cf7aa2-e55b-466b-9bd5-1b074545905a
-- title:
--   P2 M Ground Theory Heights  Heights Model Bundles Agree hypotheses inhabited 1f0479b43ccd: P2 M Ground Theory Heights  Heights Model Bundles Agree hypotheses inhabited 1f0479b43ccd
-- statement:
--   The P2 M Ground Theory Heights  Heights Model Bundles Agree hypotheses inhabited 1f0479b43ccd construction uses the P2 M Ground Theory Heights  Heights Model Bundles Agree hypotheses inhabited 1f0479b43ccd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/Statements.lean#L510-L519
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/Statements.lean#L510-L519

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_Objects
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_BundleObjects
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_Statements
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
open NumbersDVR ReciprocityTheory.ChartRestriction.G.Geo

theorem P2M_GroundTheory_Heights__Heights_Model_BundlesAgree_hypotheses_inhabited_1f0479b43ccd :
    IsIntegral SpecZ ∧ IsLocallyNoetherian SpecZ ∧ IsNormalScheme SpecZ ∧
      IsVectorBundle (structureModule SpecZ) ∧
      ∀ x : SpecZ, ringKrullDim (SpecZ.presheaf.stalk x) = 1 →
        (genericImage (structureModule SpecZ) x).map
          (LinearEquiv.refl (SpecZ.presheaf.stalk (genericPoint SpecZ))
            ((structureModule SpecZ).presheaf.stalk (genericPoint SpecZ))).toAddMonoidHom =
          genericImage (structureModule SpecZ) x := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Model».«BundlesAgree».«hypotheses_inhabited» := P2M_GroundTheory_Heights__Heights_Model_BundlesAgree_hypotheses_inhabited_1f0479b43ccd
