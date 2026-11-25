-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_gbamix_maDensity_interp
-- name    : ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.gbamix_maDensity_interp
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T14:11:56.194908+00:00
-- url     : https://prove2.me/theorems/c72e2c4d-8d01-5bee-bb91-285dba8cebe7
-- title:
--   Arakelov Geometry: gbamix ma Density interp
-- statement:
--   The Arakelov Geometry construction uses the gbamix ma Density interp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovGeometry/AMixSt.lean#L67-L111
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovGeometry/AMixSt.lean#L67-L111

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_AInterpSt
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_MdiscSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_CasChainA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_AMixSt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.GeometryOfNumbersTheory MvPolynomial MeasureTheory Module Filter Asymptotics
open scoped ComplexOrder Topology ContDiff
variable {Ω : Type} [Field Ω] [CharZero Ω] {κ : Type} [Fintype κ] {D : ℕ}

theorem ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.gbamix_maDensity_interp {m₀ m₁ : ConeMetric ℂ (Ix κ)} (h₀ : IsSmoothMetric m₀)
    (h₁ : IsSmoothMetric m₁) (t : ℝ) {γ : (Fin D → ℂ) → Ix κ → ℂ} {y : Fin D → ℂ}
    (hγ : ∀ᶠ y' in 𝓝 y, DifferentiableAt ℂ γ y' ∧ γ y' ≠ 0) :
    maDensity (fun j y' => purePot (interp m₀ m₁ t) D j (γ y')) y =
      ∑ i ∈ Finset.range (D + 1), (D.choose i : ℝ) * t ^ i * (1 - t) ^ (D - i) *
        maDensity (fun j y' => mixPot m₀ m₁ D i j (γ y')) y := by sorry
