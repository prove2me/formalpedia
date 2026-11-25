-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_GoodChartZeroSet_segre_of_isEmpty_e030d840b915
-- name    : P2M_GroundTheory_Heights__Heights_GoodChartZeroSet_segre_of_isEmpty_e030d840b915
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T03:18:29.289589+00:00
-- url     : https://prove2.me/theorems/4cf88165-31a5-4a5a-b88b-5278cf2d8235
-- title:
--   P2 M Ground Theory Heights  Heights Good Chart Zero Set segre of is Empty e030d840b915: P2 M Ground Theory Heights  Heights Good Chart Zero Set segre of is Empty e030d840b915
-- statement:
--   The P2 M Ground Theory Heights  Heights Good Chart Zero Set segre of is Empty e030d840b915 construction uses the P2 M Ground Theory Heights  Heights Good Chart Zero Set segre of is Empty e030d840b915 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PGoodChartZeroSet.lean#L82-L83
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PGoodChartZeroSet.lean#L82-L83

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

theorem P2M_GroundTheory_Heights__Heights_GoodChartZeroSet_segre_of_isEmpty_e030d840b915 (hK : IsEmpty K) (z : (Σ k, ι k) → ℂ) (j : (k : K) → ι k) : segre z j = 1 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«GoodChartZeroSet».«segre_of_isEmpty» := P2M_GroundTheory_Heights__Heights_GoodChartZeroSet_segre_of_isEmpty_e030d840b915
