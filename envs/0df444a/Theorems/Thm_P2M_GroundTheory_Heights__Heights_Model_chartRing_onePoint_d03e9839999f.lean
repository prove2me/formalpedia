-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Model_chartRing_onePoint_d03e9839999f
-- name    : P2M_GroundTheory_Heights__Heights_Model_chartRing_onePoint_d03e9839999f
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T04:37:03.206969+00:00
-- url     : https://prove2.me/theorems/9881af53-e07b-4136-9a64-f622c782006e
-- title:
--   P2 M Ground Theory Heights  Heights Model chart Ring one Point d03e9839999f: P2 M Ground Theory Heights  Heights Model chart Ring one Point d03e9839999f
-- statement:
--   The P2 M Ground Theory Heights  Heights Model chart Ring one Point d03e9839999f construction uses the P2 M Ground Theory Heights  Heights Model chart Ring one Point d03e9839999f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/Statements.lean#L653-L659
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/Statements.lean#L653-L659

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

theorem P2M_GroundTheory_Heights__Heights_Model_chartRing_onePoint_d03e9839999f (o : Type) [CommRing o] [Algebra o ℚ] :
    chartRing o onePoint () = ⊥ := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Model».«chartRing_onePoint» := P2M_GroundTheory_Heights__Heights_Model_chartRing_onePoint_d03e9839999f
