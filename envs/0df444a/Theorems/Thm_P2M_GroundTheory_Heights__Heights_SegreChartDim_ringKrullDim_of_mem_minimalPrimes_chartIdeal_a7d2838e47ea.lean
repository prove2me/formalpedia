-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_SegreChartDim_ringKrullDim_of_mem_minimalPrimes_chartIdeal_a7d2838e47ea
-- name    : P2M_GroundTheory_Heights__Heights_SegreChartDim_ringKrullDim_of_mem_minimalPrimes_chartIdeal_a7d2838e47ea
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T16:18:10.522973+00:00
-- url     : https://prove2.me/theorems/ed04941f-52d1-48fa-baf0-e397519c6670
-- title:
--   P2 M Ground Theory Heights  Heights Segre Chart Dim ring Krull Dim of mem minimal Primes chart Ideal a7d2838e47ea: P2 M Ground Theory Heights  Heights Segre Chart Dim ring Krull Dim of mem minimal Pri
-- statement:
--   The P2 M Ground Theory Heights  Heights Segre Chart Dim ring Krull Dim of mem minimal Primes chart Ideal a7d2838e47ea construction uses the P2 M Ground Theory Heights  Heights Segre Chart Dim ring Krull Dim of mem minimal Primes chart Ideal a7d2838e47ea property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PSegreChartDim.lean#L93-L126
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PSegreChartDim.lean#L93-L126

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
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
open ReciprocityTheory.AnForm.R (chartIdeal conePts affCoord)

theorem P2M_GroundTheory_Heights__Heights_SegreChartDim_ringKrullDim_of_mem_minimalPrimes_chartIdeal_a7d2838e47ea {P : Ideal (MvPolynomial (Σ k, ι k) ℂ)}
    (hP : ReciprocityTheory.AnForm.R.IsMultiHomogIdeal P) (e : ℕ)
    (hdim : ∀ Q ∈ P.minimalPrimes,
      ringKrullDim (MvPolynomial (Σ k, ι k) ℂ ⧸ Q) = ((e + Fintype.card K : ℕ) : WithBot ℕ∞))
    (p : (k : K) → ι k) {𝔮 : Ideal (MvPolynomial (Σ k, ι k) ℂ)} (h𝔮 : 𝔮 ∈ (chartIdeal P p).minimalPrimes) :
    ringKrullDim (MvPolynomial (Σ k, ι k) ℂ ⧸ 𝔮) = e := by sorry

alias «GroundTheory».«Heights₂».«Heights».«SegreChartDim».«ringKrullDim_of_mem_minimalPrimes_chartIdeal» := P2M_GroundTheory_Heights__Heights_SegreChartDim_ringKrullDim_of_mem_minimalPrimes_chartIdeal_a7d2838e47ea
