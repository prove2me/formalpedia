-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Targets_ChartSectionNotMem_ringKrullDim_ker_coneMap_ba41facb84b4
-- name    : P2M_GroundTheory_Heights__Heights_Targets_ChartSectionNotMem_ringKrullDim_ker_coneMap_ba41facb84b4
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T16:28:50.506339+00:00
-- url     : https://prove2.me/theorems/a2c6f87d-3114-45d8-b7b9-4c58c7b817a9
-- title:
--   P2 M Ground Theory Heights  Heights Targets Chart Section Not Mem ring Krull Dim ker cone Map ba41facb84b4: P2 M Ground Theory Heights  Heights Targets Chart Section Not Mem ring Krull Dim ker cone Ma
-- statement:
--   The P2 M Ground Theory Heights  Heights Targets Chart Section Not Mem ring Krull Dim ker cone Map ba41facb84b4 construction uses the P2 M Ground Theory Heights  Heights Targets Chart Section Not Mem ring Krull Dim ker cone Map ba41facb84b4 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PChartSectionNotMem.lean#L52-L160
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PChartSectionNotMem.lean#L52-L160

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StChartSection
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PSegreChartDim
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_IsSmoothMetricOfIsSmoothHerm
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_ConeChart
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_BaseChangeC
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_IntToRat
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_KleimanNefness_AlgDim
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterBridgeB
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PChartSectionNotMem
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
open MvPolynomial Algebra
open ReciprocityTheory.ChartRestriction.G.Geo (MRing IsArithVar IsSectionOn mcPts segre)
open GroundTheory.Heights₂.Heights.Targets.ChartSectionNotMem
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
set_option maxHeartbeats 1000000

theorem P2M_GroundTheory_Heights__Heights_Targets_ChartSectionNotMem_ringKrullDim_ker_coneMap_ba41facb84b4 (𝔮 : Ideal (MvPolynomial (Σ k, ι k) ℂ)) [𝔮.IsPrime] (p : (k : K) → ι k)
    (h1 : ∀ k, (X ⟨k, p k⟩ - 1 : MvPolynomial (Σ k, ι k) ℂ) ∈ 𝔮) (d : ℕ)
    (hd : ringKrullDim (MvPolynomial (Σ k, ι k) ℂ ⧸ 𝔮) = (d : WithBot ℕ∞)) :
    ringKrullDim (MvPolynomial (Σ k, ι k) ℂ ⧸ RingHom.ker (coneMap (K := K) 𝔮)) =
      ((d + Fintype.card K : ℕ) : WithBot ℕ∞) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Targets».«ChartSectionNotMem».«ringKrullDim_ker_coneMap» := P2M_GroundTheory_Heights__Heights_Targets_ChartSectionNotMem_ringKrullDim_ker_coneMap_ba41facb84b4
