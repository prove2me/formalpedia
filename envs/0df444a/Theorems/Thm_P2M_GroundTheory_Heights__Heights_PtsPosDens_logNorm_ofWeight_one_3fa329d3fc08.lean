-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_PtsPosDens_logNorm_ofWeight_one_3fa329d3fc08
-- name    : P2M_GroundTheory_Heights__Heights_PtsPosDens_logNorm_ofWeight_one_3fa329d3fc08
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:44:10.250937+00:00
-- url     : https://prove2.me/theorems/58546c2d-4d0b-4751-bc8d-10f4aa464ce4
-- title:
--   P2 M Ground Theory Heights  Heights Pts Pos Dens log Norm of Weight one 3fa329d3fc08: P2 M Ground Theory Heights  Heights Pts Pos Dens log Norm of Weight one 3fa329d3fc08
-- statement:
--   The P2 M Ground Theory Heights  Heights Pts Pos Dens log Norm of Weight one 3fa329d3fc08 construction uses the P2 M Ground Theory Heights  Heights Pts Pos Dens log Norm of Weight one 3fa329d3fc08 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PtsPosDensMeasurable.lean#L17-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PtsPosDensMeasurable.lean#L17-L20

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StPtsPosDensIntegrable
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PtsSumMeasurableA
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_NoCommonComponentCoordinatesPlane
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PtsPosDensMeasurable
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
open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.ChartRestriction.G.Geo InnerProductSpace Laplacian
open GroundTheory.Heights₂.Heights.PtsPosDens
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem P2M_GroundTheory_Heights__Heights_PtsPosDens_logNorm_ofWeight_one_3fa329d3fc08 {g : ((Σ k, ι k) → ℂ) → ℝ} (hg : IsDegZeroSmooth g) :
    logNorm (HermLine.ofWeight g hg.2) 1 = g := by sorry

alias «GroundTheory».«Heights₂».«Heights».«PtsPosDens».«logNorm_ofWeight_one» := P2M_GroundTheory_Heights__Heights_PtsPosDens_logNorm_ofWeight_one_3fa329d3fc08
