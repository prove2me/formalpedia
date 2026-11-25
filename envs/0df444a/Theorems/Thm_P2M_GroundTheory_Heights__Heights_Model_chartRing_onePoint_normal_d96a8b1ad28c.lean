-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Model_chartRing_onePoint_normal_d96a8b1ad28c
-- name    : P2M_GroundTheory_Heights__Heights_Model_chartRing_onePoint_normal_d96a8b1ad28c
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T03:29:27.794792+00:00
-- url     : https://prove2.me/theorems/3d39a789-2ff0-429f-af88-3f7f86087aff
-- title:
--   P2 M Ground Theory Heights  Heights Model chart Ring one Point normal d96a8b1ad28c: P2 M Ground Theory Heights  Heights Model chart Ring one Point normal d96a8b1ad28c
-- statement:
--   The P2 M Ground Theory Heights  Heights Model chart Ring one Point normal d96a8b1ad28c construction uses the P2 M Ground Theory Heights  Heights Model chart Ring one Point normal d96a8b1ad28c property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/Statements.lean#L661-L666
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/Statements.lean#L661-L666

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

theorem P2M_GroundTheory_Heights__Heights_Model_chartRing_onePoint_normal_d96a8b1ad28c :
    IsNoetherianRing (chartRing ℤ onePoint ()) ∧ IsIntegrallyClosed (chartRing ℤ onePoint ()) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Model».«chartRing_onePoint_normal» := P2M_GroundTheory_Heights__Heights_Model_chartRing_onePoint_normal_d96a8b1ad28c
