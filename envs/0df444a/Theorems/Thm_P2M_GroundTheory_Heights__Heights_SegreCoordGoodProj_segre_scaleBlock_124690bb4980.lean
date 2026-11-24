-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_SegreCoordGoodProj_segre_scaleBlock_124690bb4980
-- name    : P2M_GroundTheory_Heights__Heights_SegreCoordGoodProj_segre_scaleBlock_124690bb4980
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T01:31:25.832527+00:00
-- url     : https://prove2.me/theorems/1fd4a589-d9c9-4a7b-9a0f-814ea96897bd
-- title:
--   P2 M Ground Theory Heights  Heights Segre Coord Good Proj segre scale Block 124690bb4980: P2 M Ground Theory Heights  Heights Segre Coord Good Proj segre scale Block 124690bb4980
-- statement:
--   The P2 M Ground Theory Heights  Heights Segre Coord Good Proj segre scale Block 124690bb4980 construction uses the P2 M Ground Theory Heights  Heights Segre Coord Good Proj segre scale Block 124690bb4980 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PSegreCoordGoodProj.lean#L40-L44
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PSegreCoordGoodProj.lean#L40-L44

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterGood
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StSegreCoordGoodProj
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PSegreCoordGoodProj
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Geo
open GroundTheory.Heights₂.Heights.SegreCoordGoodProj
variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]
omit [∀ k, Fintype (ι k)]

theorem P2M_GroundTheory_Heights__Heights_SegreCoordGoodProj_segre_scaleBlock_124690bb4980 (k0 : K) (c : ℂ) (z : (Σ k, ι k) → ℂ) (t : (k : K) → ι k) :
    segre (scaleBlock k0 c z) t = c * segre z t := by sorry

alias «GroundTheory».«Heights₂».«Heights».«SegreCoordGoodProj».«segre_scaleBlock» := P2M_GroundTheory_Heights__Heights_SegreCoordGoodProj_segre_scaleBlock_124690bb4980
