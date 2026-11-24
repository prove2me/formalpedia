-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_SegreCoordGoodProj_evQ_segQ_ccbce2b0c3b4
-- name    : P2M_GroundTheory_Heights__Heights_SegreCoordGoodProj_evQ_segQ_ccbce2b0c3b4
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:22:17.454102+00:00
-- url     : https://prove2.me/theorems/f15ae08a-9bb5-4f80-852a-040d0a7094db
-- title:
--   P2 M Ground Theory Heights  Heights Segre Coord Good Proj ev Q seg Q ccbce2b0c3b4: P2 M Ground Theory Heights  Heights Segre Coord Good Proj ev Q seg Q ccbce2b0c3b4
-- statement:
--   The P2 M Ground Theory Heights  Heights Segre Coord Good Proj ev Q seg Q ccbce2b0c3b4 construction uses the P2 M Ground Theory Heights  Heights Segre Coord Good Proj ev Q seg Q ccbce2b0c3b4 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PSegreCoordGoodProj.lean#L34-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PSegreCoordGoodProj.lean#L34-L37

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

theorem P2M_GroundTheory_Heights__Heights_SegreCoordGoodProj_evQ_segQ_ccbce2b0c3b4 (P : Ideal (MRing ι)) (z : (Σ k, ι k) → ℂ) (hz : z ∈ mcPts P) (t : (k : K) → ι k) :
    evQ P z hz (segQ P t) = segre z t := by sorry

alias «GroundTheory».«Heights₂».«Heights».«SegreCoordGoodProj».«evQ_segQ» := P2M_GroundTheory_Heights__Heights_SegreCoordGoodProj_evQ_segQ_ccbce2b0c3b4
