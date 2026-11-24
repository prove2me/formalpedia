-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_GoodChartZeroSet_eval_linForm_717c7b580fff
-- name    : P2M_GroundTheory_Heights__Heights_GoodChartZeroSet_eval_linForm_717c7b580fff
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T18:05:11.902724+00:00
-- url     : https://prove2.me/theorems/6c0764d0-b32b-4669-bea7-3d33b70035fe
-- title:
--   P2 M Ground Theory Heights  Heights Good Chart Zero Set eval lin Form 717c7b580fff: P2 M Ground Theory Heights  Heights Good Chart Zero Set eval lin Form 717c7b580fff
-- statement:
--   The P2 M Ground Theory Heights  Heights Good Chart Zero Set eval lin Form 717c7b580fff construction uses the P2 M Ground Theory Heights  Heights Good Chart Zero Set eval lin Form 717c7b580fff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PGoodChartZeroSet.lean#L58-L69
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PGoodChartZeroSet.lean#L58-L69

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

theorem P2M_GroundTheory_Heights__Heights_GoodChartZeroSet_eval_linForm_717c7b580fff {m e : ℕ} (σ : Fin m ≃ ((k : K) → ι k))
    (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)) (x : Fin m → ℂ) :
    eval x (linForm σ Ψ) = Ψ (fun i' => x (σ.symm i')) 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«GoodChartZeroSet».«eval_linForm» := P2M_GroundTheory_Heights__Heights_GoodChartZeroSet_eval_linForm_717c7b580fff
