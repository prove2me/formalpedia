-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Model_ChartBundlesAgree_hypotheses_inhabited_102eeb634127
-- name    : P2M_GroundTheory_Heights__Heights_Model_ChartBundlesAgree_hypotheses_inhabited_102eeb634127
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T03:50:13.888936+00:00
-- url     : https://prove2.me/theorems/4b0e5eec-f6d1-5b26-a2a4-d4b2d74bce08
-- title:
--   P2 M Ground Theory Heights  Heights Model Chart Bundles Agree hypotheses inhabited 102eeb634127: P2 M Ground Theory Heights  Heights Model Chart Bundles Agree hypotheses inhabited 102eeb634127
-- statement:
--   The P2 M Ground Theory Heights  Heights Model Chart Bundles Agree hypotheses inhabited 102eeb634127 construction uses the P2 M Ground Theory Heights  Heights Model Chart Bundles Agree hypotheses inhabited 102eeb634127 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/Statements.lean#L668-L674
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/Statements.lean#L668-L674

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

theorem P2M_GroundTheory_Heights__Heights_Model_ChartBundlesAgree_hypotheses_inhabited_102eeb634127 :
    IsNoetherianRing (chartRing ℤ onePoint ()) ∧ IsIntegrallyClosed (chartRing ℤ onePoint ()) ∧
      ∀ v ∈ (scaledTrivBundle ℤ onePoint 1 (one_ne_zero (α := ℚ))).lat (),
        ∃ s : chartRing ℤ onePoint (), s ≠ 0 ∧
          (s : ℚ) • v ∈ (scaledTrivBundle ℤ onePoint 1 (one_ne_zero (α := ℚ))).lat () := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Model».«ChartBundlesAgree».«hypotheses_inhabited» := P2M_GroundTheory_Heights__Heights_Model_ChartBundlesAgree_hypotheses_inhabited_102eeb634127
