-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_PointsBilinear_sheetDensity_sum_left_f5fa1d80af90
-- name    : P2M_GroundTheory_Heights__Heights_PointsBilinear_sheetDensity_sum_left_f5fa1d80af90
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T04:16:25.573795+00:00
-- url     : https://prove2.me/theorems/c508a7cd-0a51-4519-85e5-d5e4fe21bb7c
-- title:
--   P2 M Ground Theory Heights  Heights Points Bilinear sheet Density sum left f5fa1d80af90: P2 M Ground Theory Heights  Heights Points Bilinear sheet Density sum left f5fa1d80af90
-- statement:
--   The P2 M Ground Theory Heights  Heights Points Bilinear sheet Density sum left f5fa1d80af90 construction uses the P2 M Ground Theory Heights  Heights Points Bilinear sheet Density sum left f5fa1d80af90 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PPtsBilinear.lean#L93-L101
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PPtsBilinear.lean#L93-L101

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_MdiscSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_CasChainA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterSheet
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StPtsBilinear
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PtsIntegrable
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PPtsBilinear
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
open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.ChartRestriction.G.Geo
open scoped ContDiff
open GroundTheory.Heights₂.Heights.PointsBilinear
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
omit [∀ k, Fintype (ι k)]

theorem P2M_GroundTheory_Heights__Heights_PointsBilinear_sheetDensity_sum_left_f5fa1d80af90 {n : ℕ} (P : Ideal (MRing ι))
    (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (n + 1) → ℂ)) (φ : Fin n → ((Σ k, ι k) → ℂ) → ℝ)
    {T : Type} [Fintype T] (u : T → ((Σ k, ι k) → ℂ) → ℝ) (y : Fin n → ℂ)
    (w : ((k : K) → ι k) → ℂ) :
    sheetDensity P Ψ φ (fun z => ∑ t, u t z) y w = ∑ t, sheetDensity P Ψ φ (u t) y w := by sorry

alias «GroundTheory».«Heights₂».«Heights».«PointsBilinear».«sheetDensity_sum_left» := P2M_GroundTheory_Heights__Heights_PointsBilinear_sheetDensity_sum_left_f5fa1d80af90
