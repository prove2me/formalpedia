-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_homogeneousComponent_mem_leadIdeal_8a73b12138bb
-- name    : P2M_GroundTheory_Heights__Heights_homogeneousComponent_mem_leadIdeal_8a73b12138bb
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T16:35:59.097597+00:00
-- url     : https://prove2.me/theorems/e1285895-3da9-4d0b-8f46-d84623f56782
-- title:
--   P2 M Ground Theory Heights  Heights homogeneous Component mem lead Ideal 8a73b12138bb: P2 M Ground Theory Heights  Heights homogeneous Component mem lead Ideal 8a73b12138bb
-- statement:
--   The P2 M Ground Theory Heights  Heights homogeneous Component mem lead Ideal 8a73b12138bb construction uses the P2 M Ground Theory Heights  Heights homogeneous Component mem lead Ideal 8a73b12138bb property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PSegreChartProjFinite.lean#L16-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PSegreChartProjFinite.lean#L16-L23

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StSegreChartProjFinite
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PSegreChartDim
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PFiniteProjHomInjective
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PConeAvoidsFinite
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterFib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PSegreChartProjFinite
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

theorem P2M_GroundTheory_Heights__Heights_homogeneousComponent_mem_leadIdeal_8a73b12138bb {n : ℕ} {J : Ideal (MvPolynomial (Fin n) ℂ)}
    {f : MvPolynomial (Fin n) ℂ} (hf : f ∈ J) {r : ℕ} (hr : f.totalDegree ≤ r) :
    homogeneousComponent r f ∈ leadIdeal J := by sorry

alias «GroundTheory».«Heights₂».«Heights».«homogeneousComponent_mem_leadIdeal» := P2M_GroundTheory_Heights__Heights_homogeneousComponent_mem_leadIdeal_8a73b12138bb
