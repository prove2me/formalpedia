-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_GoodChartZeroSet_eval_homogenize_c2c6fe846b43
-- name    : P2M_GroundTheory_Heights__Heights_GoodChartZeroSet_eval_homogenize_c2c6fe846b43
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T03:18:56.801557+00:00
-- url     : https://prove2.me/theorems/74721a62-89fa-4ed8-be77-6d4de0907182
-- title:
--   P2 M Ground Theory Heights  Heights Good Chart Zero Set eval homogenize c2c6fe846b43: P2 M Ground Theory Heights  Heights Good Chart Zero Set eval homogenize c2c6fe846b43
-- statement:
--   The P2 M Ground Theory Heights  Heights Good Chart Zero Set eval homogenize c2c6fe846b43 construction uses the P2 M Ground Theory Heights  Heights Good Chart Zero Set eval homogenize c2c6fe846b43 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PGoodChartZeroSet.lean#L23-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PGoodChartZeroSet.lean#L23-L39

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StGoodChartZeroSet
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PSegreChartZeroSet
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_EvalSmulOfIsHomogeneousAlt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PGoodChartZeroSet
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_scaleBlock_mem_zeroLocus

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
open MvPolynomial Finset
open ReciprocityTheory.ChartRestriction.G.Geo (MRing IsMultiHomogIdeal mcPts segre scaleBlock scaleBlock_mem_zeroLocus)
open ComplexSets
open GroundTheory.Heights₂.Heights.GoodChartZeroSet

theorem P2M_GroundTheory_Heights__Heights_GoodChartZeroSet_eval_homogenize_c2c6fe846b43 {m : ℕ} (f : MvPolynomial (Fin m) ℂ) {D : ℕ} (hD : f.totalDegree ≤ D) (a : Fin m)
    (w : Fin m → ℂ) (hw : w a ≠ 0) :
    eval w (X a * ∑ d ∈ range (D + 1), X a ^ (D - d) * homogeneousComponent d f) =
      w a ^ (D + 1) * eval ((w a)⁻¹ • w) f := by sorry

alias «GroundTheory».«Heights₂».«Heights».«GoodChartZeroSet».«eval_homogenize» := P2M_GroundTheory_Heights__Heights_GoodChartZeroSet_eval_homogenize_c2c6fe846b43
