-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Targets_SegreChartIntegralPoints_minimalPrimes_vanishingIdeal_ad3abc2fc98d
-- name    : P2M_GroundTheory_Heights__Heights_Targets_SegreChartIntegralPoints_minimalPrimes_vanishingIdeal_ad3abc2fc98d
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T14:06:28.472619+00:00
-- url     : https://prove2.me/theorems/0d7f14cf-af17-4e58-b134-e3f0a9e24bbc
-- title:
--   P2 M Ground Theory Heights  Heights Targets Segre Chart Integral Points minimal Primes vanishing Ideal ad3abc2fc98d: P2 M Ground Theory Heights  Heights Targets Segre Chart Integral Points minimal Pri
-- statement:
--   The P2 M Ground Theory Heights  Heights Targets Segre Chart Integral Points minimal Primes vanishing Ideal ad3abc2fc98d construction uses the P2 M Ground Theory Heights  Heights Targets Segre Chart Integral Points minimal Primes vanishing Ideal ad3abc2fc98d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PSegreChartIntegralPoints.lean#L25-L55
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PSegreChartIntegralPoints.lean#L25-L55

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

theorem P2M_GroundTheory_Heights__Heights_Targets_SegreChartIntegralPoints_minimalPrimes_vanishingIdeal_ad3abc2fc98d {m : ℕ} {S : Set (Fin m → ℂ)} (hS : S.Finite) :
    (vanishingIdeal ℂ S : Ideal (MvPolynomial (Fin m) ℂ)).minimalPrimes =
      (fun x => RingHom.ker (eval x)) '' S := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Targets».«SegreChartIntegralPoints».«minimalPrimes_vanishingIdeal» := P2M_GroundTheory_Heights__Heights_Targets_SegreChartIntegralPoints_minimalPrimes_vanishingIdeal_ad3abc2fc98d
