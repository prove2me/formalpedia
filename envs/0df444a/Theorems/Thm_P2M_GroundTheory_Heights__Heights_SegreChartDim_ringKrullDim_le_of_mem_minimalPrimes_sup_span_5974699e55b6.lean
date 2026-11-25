-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_SegreChartDim_ringKrullDim_le_of_mem_minimalPrimes_sup_span_5974699e55b6
-- name    : P2M_GroundTheory_Heights__Heights_SegreChartDim_ringKrullDim_le_of_mem_minimalPrimes_sup_span_5974699e55b6
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T16:15:46.842801+00:00
-- url     : https://prove2.me/theorems/fc5c2992-117b-4b1a-8248-7e2350871aaa
-- title:
--   P2 M Ground Theory Heights  Heights Segre Chart Dim ring Krull Dim le of mem minimal Primes sup span 5974699e55b6: P2 M Ground Theory Heights  Heights Segre Chart Dim ring Krull Dim le of mem minimal
-- statement:
--   The P2 M Ground Theory Heights  Heights Segre Chart Dim ring Krull Dim le of mem minimal Primes sup span 5974699e55b6 construction uses the P2 M Ground Theory Heights  Heights Segre Chart Dim ring Krull Dim le of mem minimal Primes sup span 5974699e55b6 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PSegreChartDim.lean#L52-L87
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PSegreChartDim.lean#L52-L87

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StSegreChartDim
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_IsSmoothMetricOfIsSmoothHerm
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_ConeChart
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_BaseChangeC
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_KleimanNefness_AlgDim
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PSegreChartDim
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
open ReciprocityTheory.ChartRestriction.G.Geo (MRing IsArithVar mcPts segre)
open GroundTheory.Heights₂.Heights.SegreChartDim

theorem P2M_GroundTheory_Heights__Heights_SegreChartDim_ringKrullDim_le_of_mem_minimalPrimes_sup_span_5974699e55b6 {F : Type} [Field F] {τ : Type} [Fintype τ]
    (s : Finset (MvPolynomial τ F)) :
    ∀ (V W : Ideal (MvPolynomial τ F)), V.IsPrime → W ∈ (V ⊔ Ideal.span (s : Set (MvPolynomial τ F))).minimalPrimes →
      ringKrullDim (MvPolynomial τ F ⧸ V) ≤ ringKrullDim (MvPolynomial τ F ⧸ W) + (s.card : WithBot ℕ∞) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«SegreChartDim».«ringKrullDim_le_of_mem_minimalPrimes_sup_span» := P2M_GroundTheory_Heights__Heights_SegreChartDim_ringKrullDim_le_of_mem_minimalPrimes_sup_span_5974699e55b6
