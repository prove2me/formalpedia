-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_PointsBilinear_sheetDensity_sum_right_576edd36545f
-- name    : P2M_GroundTheory_Heights__Heights_PointsBilinear_sheetDensity_sum_right_576edd36545f
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T04:15:35.668889+00:00
-- url     : https://prove2.me/theorems/f63be69a-fdf3-4d5a-ac08-f0316fb6dc39
-- title:
--   P2 M Ground Theory Heights  Heights Points Bilinear sheet Density sum right 576edd36545f: P2 M Ground Theory Heights  Heights Points Bilinear sheet Density sum right 576edd36545f
-- statement:
--   The P2 M Ground Theory Heights  Heights Points Bilinear sheet Density sum right 576edd36545f construction uses the P2 M Ground Theory Heights  Heights Points Bilinear sheet Density sum right 576edd36545f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PPtsBilinear.lean#L103-L116
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PPtsBilinear.lean#L103-L116

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

theorem P2M_GroundTheory_Heights__Heights_PointsBilinear_sheetDensity_sum_right_576edd36545f {n : ℕ} (P : Ideal (MRing ι))
    (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (n + 1 + 1) → ℂ)) (L : Fin n → HermLine ι)
    {T : Type} [Fintype T] {u : T → ((Σ k, ι k) → ℂ) → ℝ} (hu : ∀ t, IsDegZeroSmooth (u t))
    (g : ((Σ k, ι k) → ℂ) → ℝ) (y : Fin (n + 1) → ℂ) (w : ((k : K) → ι k) → ℂ) :
    sheetDensity P Ψ (Fin.cons (fun z => ∑ t, u t z) (pot L)) g y w =
      ∑ t, sheetDensity P Ψ (Fin.cons (u t) (pot L)) g y w := by sorry

alias «GroundTheory».«Heights₂».«Heights».«PointsBilinear».«sheetDensity_sum_right» := P2M_GroundTheory_Heights__Heights_PointsBilinear_sheetDensity_sum_right_576edd36545f
