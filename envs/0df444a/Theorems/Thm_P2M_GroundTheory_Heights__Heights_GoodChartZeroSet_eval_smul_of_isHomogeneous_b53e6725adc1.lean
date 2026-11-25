-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_GoodChartZeroSet_eval_smul_of_isHomogeneous_b53e6725adc1
-- name    : P2M_GroundTheory_Heights__Heights_GoodChartZeroSet_eval_smul_of_isHomogeneous_b53e6725adc1
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T18:05:05.834279+00:00
-- url     : https://prove2.me/theorems/2340e669-5454-478f-b2cd-b45bb2f26d34
-- title:
--   P2 M Ground Theory Heights  Heights Good Chart Zero Set eval smul of is Homogeneous b53e6725adc1: P2 M Ground Theory Heights  Heights Good Chart Zero Set eval smul of is Homogeneous b53e6725adc1
-- statement:
--   The P2 M Ground Theory Heights  Heights Good Chart Zero Set eval smul of is Homogeneous b53e6725adc1 construction uses the P2 M Ground Theory Heights  Heights Good Chart Zero Set eval smul of is Homogeneous b53e6725adc1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PGoodChartZeroSet.lean#L19-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PGoodChartZeroSet.lean#L19-L21

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

theorem P2M_GroundTheory_Heights__Heights_GoodChartZeroSet_eval_smul_of_isHomogeneous_b53e6725adc1 {τ : Type*} {φ : MvPolynomial τ ℂ} {n : ℕ} (hφ : φ.IsHomogeneous n)
    (c : ℂ) (w : τ → ℂ) : eval (c • w) φ = c ^ n * eval w φ := by sorry

alias «GroundTheory».«Heights₂».«Heights».«GoodChartZeroSet».«eval_smul_of_isHomogeneous» := P2M_GroundTheory_Heights__Heights_GoodChartZeroSet_eval_smul_of_isHomogeneous_b53e6725adc1
