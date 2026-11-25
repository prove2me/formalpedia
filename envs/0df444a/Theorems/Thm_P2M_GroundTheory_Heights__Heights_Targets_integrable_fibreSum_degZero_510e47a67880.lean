-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Targets_integrable_fibreSum_degZero_510e47a67880
-- name    : P2M_GroundTheory_Heights__Heights_Targets_integrable_fibreSum_degZero_510e47a67880
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T08:09:56.011515+00:00
-- url     : https://prove2.me/theorems/4f88dccc-5523-43cb-b133-f6c3183a9417
-- title:
--   P2 M Ground Theory Heights  Heights Targets integrable fibre Sum deg Zero 510e47a67880: P2 M Ground Theory Heights  Heights Targets integrable fibre Sum deg Zero 510e47a67880
-- statement:
--   The P2 M Ground Theory Heights  Heights Targets integrable fibre Sum deg Zero 510e47a67880 construction uses the P2 M Ground Theory Heights  Heights Targets integrable fibre Sum deg Zero 510e47a67880 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PLelongSectionLimit.lean#L32-L44
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PLelongSectionLimit.lean#L32-L44

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

theorem P2M_GroundTheory_Heights__Heights_Targets_integrable_fibreSum_degZero_510e47a67880 (hInt : PtsIntegrableStatement) {Q : Ideal (MRing ι)} {e : ℕ}
    (hQ : IsArithVar Q (e + 1)) {Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)} (hΨ : IsGoodProj Q Ψ)
    {L : Fin e → HermLine ι} (hL : ∀ j, IsSmoothHerm (L j)) {u : ((Σ k, ι k) → ℂ) → ℝ}
    (hu : IsDegZeroSmooth u) :
    Integrable (fun y => ∑ᶠ w ∈ fibre Q Ψ y, sheetDensity Q Ψ (pot L) u y w) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Targets».«integrable_fibreSum_degZero» := P2M_GroundTheory_Heights__Heights_Targets_integrable_fibreSum_degZero_510e47a67880
