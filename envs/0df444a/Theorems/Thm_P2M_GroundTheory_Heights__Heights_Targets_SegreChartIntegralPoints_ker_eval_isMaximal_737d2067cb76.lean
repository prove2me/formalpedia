-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Targets_SegreChartIntegralPoints_ker_eval_isMaximal_737d2067cb76
-- name    : P2M_GroundTheory_Heights__Heights_Targets_SegreChartIntegralPoints_ker_eval_isMaximal_737d2067cb76
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T13:59:03.659856+00:00
-- url     : https://prove2.me/theorems/63467664-1691-4439-8e6a-de9bdca188a6
-- title:
--   P2 M Ground Theory Heights  Heights Targets Segre Chart Integral Points ker eval is Maximal 737d2067cb76: P2 M Ground Theory Heights  Heights Targets Segre Chart Integral Points ker eval is Maximal 73
-- statement:
--   The P2 M Ground Theory Heights  Heights Targets Segre Chart Integral Points ker eval is Maximal 737d2067cb76 construction uses the P2 M Ground Theory Heights  Heights Targets Segre Chart Integral Points ker eval is Maximal 737d2067cb76 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PSegreChartIntegralPoints.lean#L21-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PSegreChartIntegralPoints.lean#L21-L23

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StSegreChartIntegralPoints
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_ExistsIsSheetFinZero
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_PPointIntegral
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PSegreChartIntegralPoints
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_chartLift_segre_apply_6eeb1c8817f9
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_mem_segreChartComponents_1a9d50ef3666
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_mcPts_smul
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_sameOrbit_of_segre
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_segre_smul

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
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Targets
open MvPolynomial Filter Topology
open ReciprocityTheory.ChartRestriction.G.Geo (MRing HermLine IsArithVar IsMultiHomogIdeal ptsIntegral pot segre mcPts SameOrbit
  segre_smul mcPts_smul sameOrbit_of_segre)
open GroundTheory.Heights₂.Heights (varInt IsDegZeroSmooth segreChartSet segreChartComponents segreChartIdeal chartLift
  chartLift_segre_apply mem_segreChartComponents)
open GroundTheory.Heights₂.Heights.Targets.SegreChartIntegralPoints

theorem P2M_GroundTheory_Heights__Heights_Targets_SegreChartIntegralPoints_ker_eval_isMaximal_737d2067cb76 {m : ℕ} (x : Fin m → ℂ) :
    (RingHom.ker (eval x : MvPolynomial (Fin m) ℂ →+* ℂ)).IsMaximal := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Targets».«SegreChartIntegralPoints».«ker_eval_isMaximal» := P2M_GroundTheory_Heights__Heights_Targets_SegreChartIntegralPoints_ker_eval_isMaximal_737d2067cb76
