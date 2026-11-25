-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_PointsBilinear_maDensity_cons_sum_0987d643b948
-- name    : P2M_GroundTheory_Heights__Heights_PointsBilinear_maDensity_cons_sum_0987d643b948
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T04:16:38.82889+00:00
-- url     : https://prove2.me/theorems/7f2171bc-8a42-4f8a-8a1f-8859cb934df6
-- title:
--   P2 M Ground Theory Heights  Heights Points Bilinear ma Density cons sum 0987d643b948: P2 M Ground Theory Heights  Heights Points Bilinear ma Density cons sum 0987d643b948
-- statement:
--   The P2 M Ground Theory Heights  Heights Points Bilinear ma Density cons sum 0987d643b948 construction uses the P2 M Ground Theory Heights  Heights Points Bilinear ma Density cons sum 0987d643b948 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PPtsBilinear.lean#L72-L89
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PPtsBilinear.lean#L72-L89

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

theorem P2M_GroundTheory_Heights__Heights_PointsBilinear_maDensity_cons_sum_0987d643b948 {n : ℕ} (L : Fin n → HermLine ι) {T : Type} [Fintype T]
    {u : T → ((Σ k, ι k) → ℂ) → ℝ} (hu : ∀ t, IsDegZeroSmooth (u t))
    {γ : (Fin (n + 1) → ℂ) → (Σ k, ι k) → ℂ} {y : Fin (n + 1) → ℂ}
    (hγ : ∀ᶠ y' in 𝓝 y, DifferentiableAt ℂ γ y' ∧ ∀ k, ∃ i, γ y' ⟨k, i⟩ ≠ 0) :
    maDensity (fun j y' => (Fin.cons (fun z => ∑ t, u t z) (pot L) :
        Fin (n + 1) → ((Σ k, ι k) → ℂ) → ℝ) j (γ y')) y =
      ∑ t, maDensity (fun j y' => (Fin.cons (u t) (pot L) :
        Fin (n + 1) → ((Σ k, ι k) → ℂ) → ℝ) j (γ y')) y := by sorry

alias «GroundTheory».«Heights₂».«Heights».«PointsBilinear».«maDensity_cons_sum» := P2M_GroundTheory_Heights__Heights_PointsBilinear_maDensity_cons_sum_0987d643b948
