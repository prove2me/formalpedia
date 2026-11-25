-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_GoodChartModel_homogeneousComponent_mem_leadIdeal_8ae2b33245f6
-- name    : P2M_GroundTheory_Heights__Heights_GoodChartModel_homogeneousComponent_mem_leadIdeal_8ae2b33245f6
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T14:12:24.638316+00:00
-- url     : https://prove2.me/theorems/2c3a6f57-75cc-594c-becf-daf067fee122
-- title:
--   P2 M Ground Theory Heights  Heights Good Chart Model homogeneous Component mem lead Ideal 8ae2b33245f6: P2 M Ground Theory Heights  Heights Good Chart Model homogeneous Component mem lead Ideal 8ae2b3
-- statement:
--   The P2 M Ground Theory Heights  Heights Good Chart Model homogeneous Component mem lead Ideal 8ae2b33245f6 construction uses the P2 M Ground Theory Heights  Heights Good Chart Model homogeneous Component mem lead Ideal 8ae2b33245f6 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PGoodChartModel.lean#L19-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PGoodChartModel.lean#L19-L26

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StGoodChartModel
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StGoodChartZeroSet
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StGoodChartDim
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PFiniteProjHomInjective
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PConeAvoidsFinite
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterFib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PGoodChartModel
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_segre_rel

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
open ReciprocityTheory.ChartRestriction.G.Geo (MRing IsArithVar IsGoodProj mcPts segre segre_rel)
open ComplexSets MvPolynomial Matrix
open GroundTheory.Heights₂.Heights.GoodChartModel

theorem P2M_GroundTheory_Heights__Heights_GoodChartModel_homogeneousComponent_mem_leadIdeal_8ae2b33245f6 {n : ℕ} {J : Ideal (MvPolynomial (Fin n) ℂ)}
    {f : MvPolynomial (Fin n) ℂ} (hf : f ∈ J) {r : ℕ} (hr : f.totalDegree ≤ r) :
    homogeneousComponent r f ∈ leadIdeal J := by sorry

alias «GroundTheory».«Heights₂».«Heights».«GoodChartModel».«homogeneousComponent_mem_leadIdeal» := P2M_GroundTheory_Heights__Heights_GoodChartModel_homogeneousComponent_mem_leadIdeal_8ae2b33245f6
