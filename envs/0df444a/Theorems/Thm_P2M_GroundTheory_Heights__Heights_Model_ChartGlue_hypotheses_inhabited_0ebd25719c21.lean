-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Model_ChartGlue_hypotheses_inhabited_0ebd25719c21
-- name    : P2M_GroundTheory_Heights__Heights_Model_ChartGlue_hypotheses_inhabited_0ebd25719c21
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T03:48:48.91714+00:00
-- url     : https://prove2.me/theorems/7c84988f-3d80-4cc6-aa78-b183d52ceb87
-- title:
--   P2 M Ground Theory Heights  Heights Model Chart Glue hypotheses inhabited 0ebd25719c21: P2 M Ground Theory Heights  Heights Model Chart Glue hypotheses inhabited 0ebd25719c21
-- statement:
--   The P2 M Ground Theory Heights  Heights Model Chart Glue hypotheses inhabited 0ebd25719c21 construction uses the P2 M Ground Theory Heights  Heights Model Chart Glue hypotheses inhabited 0ebd25719c21 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/Statements.lean#L716-L726
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/Statements.lean#L716-L726

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

theorem P2M_GroundTheory_Heights__Heights_Model_ChartGlue_hypotheses_inhabited_0ebd25719c21 (S : Finset Nat.Primes) (p : Nat.Primes)
    [Algebra (Localization.Away (primeProd S)) ℚ] [Algebra (ZLoc p) ℚ] :
    SameRationalSpan
      ((scaledTrivBundle (Localization.Away (primeProd S)) onePoint 1 (one_ne_zero (α := ℚ))).lat ())
      ((scaledTrivBundle (ZLoc p) onePoint 1 (one_ne_zero (α := ℚ))).lat ()) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Model».«ChartGlue».«hypotheses_inhabited» := P2M_GroundTheory_Heights__Heights_Model_ChartGlue_hypotheses_inhabited_0ebd25719c21
