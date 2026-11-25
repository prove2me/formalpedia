-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_section_basis_local_uniform_bound
-- name    : ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.section_basis_local_uniform_bound
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T10:18:41.95658+00:00
-- url     : https://prove2.me/theorems/a7426385-deb6-5818-ae4b-8702ffa4262c
-- title:
--   Arakelov Geometry: section basis local uniform bound
-- statement:
--   The Arakelov Geometry construction uses the section basis local uniform bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovGeometry/SectionBasisLocalUniformBound.lean#L25-L136
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovGeometry/SectionBasisLocalUniformBound.lean#L25-L136

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_ExistsBoundIteratedFDerivCompact
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_SectionBasisLocalUniformBound
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.GeometryOfNumbersTheory MvPolynomial MeasureTheory
open scoped ContDiff
variable {Ω : Type} [Field Ω] [CharZero Ω] {κ : Type} [Fintype κ] {D : ℕ}

theorem ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.section_basis_local_uniform_bound {x : Ix κ → Ω} {m₀ m₁ : ConeMetric ℂ (Ix κ)} {μ : Measure (Ix κ → ℂ)}
    (hg₀ : IsGood D x m₀ μ) (hg₁ : IsGood D x m₁ μ) {U C : Set (Fin D → ℂ)}
    {γ : (Fin D → ℂ) → Ix κ → ℂ} (hγ : IsParam (coordIdeal ℤ x) U γ) (hC : IsCompact C)
    (hCU : C ⊆ U) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ (n r : ℕ) (b : Fin r → MvPolynomial (Ix κ) ℚ), 1 ≤ n → IsSecBasis x n b →
      ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ y₀ ∈ C, ∀ c : Fin r → ℂ,
        ‖∑ k, c k * secFun (b k) (γ y₀)‖ ^ 2 * wgt (interp m₀ m₁ t) n (γ y₀) ≤
          M * (n : ℝ) ^ D * bNormSq μ (fun k => secFun (b k)) (wgt (interp m₀ m₁ t) n) c := by sorry
