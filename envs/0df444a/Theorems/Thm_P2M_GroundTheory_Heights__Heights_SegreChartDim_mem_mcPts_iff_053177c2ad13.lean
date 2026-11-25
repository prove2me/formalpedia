-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_SegreChartDim_mem_mcPts_iff_053177c2ad13
-- name    : P2M_GroundTheory_Heights__Heights_SegreChartDim_mem_mcPts_iff_053177c2ad13
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T16:15:48.129768+00:00
-- url     : https://prove2.me/theorems/e10d02b4-97e4-4001-9749-32c55485d0b9
-- title:
--   P2 M Ground Theory Heights  Heights Segre Chart Dim mem mc Pts iff 053177c2ad13: P2 M Ground Theory Heights  Heights Segre Chart Dim mem mc Pts iff 053177c2ad13
-- statement:
--   The P2 M Ground Theory Heights  Heights Segre Chart Dim mem mc Pts iff 053177c2ad13 construction uses the P2 M Ground Theory Heights  Heights Segre Chart Dim mem mc Pts iff 053177c2ad13 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PSegreChartDim.lean#L130-L137
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PSegreChartDim.lean#L130-L137

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StSegreChartDim
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_IsSmoothMetricOfIsSmoothHerm
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_ConeChart
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_BaseChangeC
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_KleimanNefness_AlgDim
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PSegreChartDim
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
open ReciprocityTheory.ChartRestriction.G.Geo (MRing IsArithVar mcPts segre)
open GroundTheory.Heights₂.Heights.SegreChartDim
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
omit [Fintype K] [∀ k, Fintype (ι k)]

theorem P2M_GroundTheory_Heights__Heights_SegreChartDim_mem_mcPts_iff_053177c2ad13 {P : Ideal (MRing ι)} (z : (Σ k, ι k) → ℂ) :
    z ∈ mcPts P ↔ z ∈ ReciprocityTheory.AnForm.R.conePts (P.map (MvPolynomial.map (Int.castRingHom ℂ))) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«SegreChartDim».«mem_mcPts_iff» := P2M_GroundTheory_Heights__Heights_SegreChartDim_mem_mcPts_iff_053177c2ad13
