-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Targets_SegreChartIntegralPoints_aeval_eq_eval__42e4d377e6a0
-- name    : P2M_GroundTheory_Heights__Heights_Targets_SegreChartIntegralPoints_aeval_eq_eval__42e4d377e6a0
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T13:54:30.093001+00:00
-- url     : https://prove2.me/theorems/255fd027-747d-4e7b-a464-6359e1632aa2
-- title:
--   P2 M Ground Theory Heights  Heights Targets Segre Chart Integral Points aeval eq eval  42e4d377e6a0: P2 M Ground Theory Heights  Heights Targets Segre Chart Integral Points aeval eq eval  42e4d377e6a0
-- statement:
--   The P2 M Ground Theory Heights  Heights Targets Segre Chart Integral Points aeval eq eval  42e4d377e6a0 construction uses the P2 M Ground Theory Heights  Heights Targets Segre Chart Integral Points aeval eq eval  42e4d377e6a0 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PSegreChartIntegralPoints.lean#L19-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PSegreChartIntegralPoints.lean#L19-L19

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

theorem P2M_GroundTheory_Heights__Heights_Targets_SegreChartIntegralPoints_aeval_eq_eval__42e4d377e6a0 {m : ℕ} (x : Fin m → ℂ) (p : MvPolynomial (Fin m) ℂ) : aeval x p = eval x p := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Targets».«SegreChartIntegralPoints».«aeval_eq_eval'» := P2M_GroundTheory_Heights__Heights_Targets_SegreChartIntegralPoints_aeval_eq_eval__42e4d377e6a0
