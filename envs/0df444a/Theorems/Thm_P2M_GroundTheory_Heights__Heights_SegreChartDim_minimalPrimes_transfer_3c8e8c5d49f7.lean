-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_SegreChartDim_minimalPrimes_transfer_3c8e8c5d49f7
-- name    : P2M_GroundTheory_Heights__Heights_SegreChartDim_minimalPrimes_transfer_3c8e8c5d49f7
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T16:13:27.84818+00:00
-- url     : https://prove2.me/theorems/dc602635-8df7-5ea8-a34b-ebd69b89e651
-- title:
--   P2 M Ground Theory Heights  Heights Segre Chart Dim minimal Primes transfer 3c8e8c5d49f7: P2 M Ground Theory Heights  Heights Segre Chart Dim minimal Primes transfer 3c8e8c5d49f7
-- statement:
--   The P2 M Ground Theory Heights  Heights Segre Chart Dim minimal Primes transfer 3c8e8c5d49f7 construction uses the P2 M Ground Theory Heights  Heights Segre Chart Dim minimal Primes transfer 3c8e8c5d49f7 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PSegreChartDim.lean#L18-L50
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PSegreChartDim.lean#L18-L50

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

theorem P2M_GroundTheory_Heights__Heights_SegreChartDim_minimalPrimes_transfer_3c8e8c5d49f7 {A B : Type*} [CommRing A] [CommRing B] (f : A →+* B) (g : B →+* A)
    (I : Ideal A) (I' : Ideal B) (hf : I ≤ I'.comap f) (hg : I' ≤ I.comap g)
    (hgf : ∀ a, g (f a) - a ∈ I) (hfg : ∀ b, f (g b) - b ∈ I') (J : Ideal A) (hJ : J ∈ I.minimalPrimes) :
    J.comap g ∈ I'.minimalPrimes ∧ ringKrullDim (A ⧸ J) = ringKrullDim (B ⧸ J.comap g) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«SegreChartDim».«minimalPrimes_transfer» := P2M_GroundTheory_Heights__Heights_SegreChartDim_minimalPrimes_transfer_3c8e8c5d49f7
