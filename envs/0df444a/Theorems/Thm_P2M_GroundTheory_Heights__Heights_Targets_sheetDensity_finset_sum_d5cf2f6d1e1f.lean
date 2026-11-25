-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Targets_sheetDensity_finset_sum_d5cf2f6d1e1f
-- name    : P2M_GroundTheory_Heights__Heights_Targets_sheetDensity_finset_sum_d5cf2f6d1e1f
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T08:07:14.062146+00:00
-- url     : https://prove2.me/theorems/d789406e-b145-4d40-959d-8b24a7ba5d84
-- title:
--   P2 M Ground Theory Heights  Heights Targets sheet Density finset sum d5cf2f6d1e1f: P2 M Ground Theory Heights  Heights Targets sheet Density finset sum d5cf2f6d1e1f
-- statement:
--   The P2 M Ground Theory Heights  Heights Targets sheet Density finset sum d5cf2f6d1e1f construction uses the P2 M Ground Theory Heights  Heights Targets sheet Density finset sum d5cf2f6d1e1f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PLelongSectionLimit.lean#L24-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PLelongSectionLimit.lean#L24-L30

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterFib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterDivSupp
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PPtsAddFirst
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PDeLeSemiPos
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PRFormula
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PSegrePartition
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_LogRegLineTensor
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_LelongSectionLimit
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_LelongChartLimit
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PLelongSectionLimit
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
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology MeasureTheory
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
omit [∀ k, Fintype (ι k)]

theorem P2M_GroundTheory_Heights__Heights_Targets_sheetDensity_finset_sum_d5cf2f6d1e1f {e : ℕ} (Q : Ideal (MRing ι))
    (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)) (φ : Fin e → ((Σ k, ι k) → ℂ) → ℝ)
    {T : Type*} (S : Finset T) (u : T → ((Σ k, ι k) → ℂ) → ℝ) (y : Fin e → ℂ)
    (w : ((k : K) → ι k) → ℂ) :
    sheetDensity Q Ψ φ (fun z => ∑ t ∈ S, u t z) y w = ∑ t ∈ S, sheetDensity Q Ψ φ (u t) y w := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Targets».«sheetDensity_finset_sum» := P2M_GroundTheory_Heights__Heights_Targets_sheetDensity_finset_sum_d5cf2f6d1e1f
