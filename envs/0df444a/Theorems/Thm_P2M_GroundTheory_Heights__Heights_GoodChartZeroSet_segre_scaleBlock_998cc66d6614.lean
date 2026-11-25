-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_GoodChartZeroSet_segre_scaleBlock_998cc66d6614
-- name    : P2M_GroundTheory_Heights__Heights_GoodChartZeroSet_segre_scaleBlock_998cc66d6614
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T03:21:01.669634+00:00
-- url     : https://prove2.me/theorems/39e3970a-71ae-4a70-ab7a-7353caa60a67
-- title:
--   P2 M Ground Theory Heights  Heights Good Chart Zero Set segre scale Block 998cc66d6614: P2 M Ground Theory Heights  Heights Good Chart Zero Set segre scale Block 998cc66d6614
-- statement:
--   The P2 M Ground Theory Heights  Heights Good Chart Zero Set segre scale Block 998cc66d6614 construction uses the P2 M Ground Theory Heights  Heights Good Chart Zero Set segre scale Block 998cc66d6614 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PGoodChartZeroSet.lean#L45-L50
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PGoodChartZeroSet.lean#L45-L50

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
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
omit [∀ k, Fintype (ι k)]

theorem P2M_GroundTheory_Heights__Heights_GoodChartZeroSet_segre_scaleBlock_998cc66d6614 [DecidableEq K] (k0 : K) (c : ℂ) (z : (Σ k, ι k) → ℂ) :
    segre (scaleBlock k0 c z) = c • segre z := by sorry

alias «GroundTheory».«Heights₂».«Heights».«GoodChartZeroSet».«segre_scaleBlock» := P2M_GroundTheory_Heights__Heights_GoodChartZeroSet_segre_scaleBlock_998cc66d6614
