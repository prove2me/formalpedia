-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_SegreChartZeroSet_eval_liftPoly_7a6b03adb6c3
-- name    : P2M_GroundTheory_Heights__Heights_SegreChartZeroSet_eval_liftPoly_7a6b03adb6c3
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T04:37:47.35682+00:00
-- url     : https://prove2.me/theorems/44100518-408c-4003-9d4c-b6cd1ee6ddd7
-- title:
--   P2 M Ground Theory Heights  Heights Segre Chart Zero Set eval lift Poly 7a6b03adb6c3: P2 M Ground Theory Heights  Heights Segre Chart Zero Set eval lift Poly 7a6b03adb6c3
-- statement:
--   The P2 M Ground Theory Heights  Heights Segre Chart Zero Set eval lift Poly 7a6b03adb6c3 construction uses the P2 M Ground Theory Heights  Heights Segre Chart Zero Set eval lift Poly 7a6b03adb6c3 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PSegreChartZeroSet.lean#L44-L51
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PSegreChartZeroSet.lean#L44-L51

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StSegreChartZeroSet
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterGood
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PSegreChartZeroSet
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
open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Geo (MRing IsMultiHomogIdeal mcPts segre scaleBlock scaleBlock_mem_zeroLocus)
open ComplexSets
open GroundTheory.Heights₂.Heights.SegreChartZeroSet
variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]
omit [Fintype K] [∀ k, Fintype (ι k)]

theorem P2M_GroundTheory_Heights__Heights_SegreChartZeroSet_eval_liftPoly_7a6b03adb6c3 {m : ℕ} (σ : Fin m ≃ ((k : K) → ι k)) (i : (k : K) → ι k) (x : Fin m → ℂ)
    (f : MRing ι) :
    eval x (liftPoly σ i f) = eval (chartLift σ i x) (map (Int.castRingHom ℂ) f) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«SegreChartZeroSet».«eval_liftPoly» := P2M_GroundTheory_Heights__Heights_SegreChartZeroSet_eval_liftPoly_7a6b03adb6c3
