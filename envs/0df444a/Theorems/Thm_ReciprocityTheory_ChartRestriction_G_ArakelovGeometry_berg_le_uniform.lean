-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_berg_le_uniform
-- name    : ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.berg_le_uniform
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T10:03:35.700984+00:00
-- url     : https://prove2.me/theorems/357226e4-58a6-5133-82db-950b331bf02d
-- title:
--   Arakelov Geometry: berg le uniform
-- statement:
--   The Arakelov Geometry construction uses the berg le uniform property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovGeometry/SupLeL2NormSections.lean#L13-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovGeometry/SupLeL2NormSections.lean#L13-L35

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_ABridgeSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_AParamSt
import Definitions.Def_ReciprocityTheory_GeometryOfNumbers_PluriharmonicAnalysis_MorseGenSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_SectionBasisLocalUniformBound
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_SupLeL2NormSections
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
open scoped ComplexOrder
variable {Ω : Type} [Field Ω] [CharZero Ω] {κ : Type} [Fintype κ] {D : ℕ}

theorem ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.berg_le_uniform {x : Ix κ → Ω} {m₀ m₁ : ConeMetric ℂ (Ix κ)} {μ : Measure (Ix κ → ℂ)}
    (hg₀ : IsGood D x m₀ μ) (hg₁ : IsGood D x m₁ μ) :
    ∃ C : ℝ, ∀ (n r : ℕ) (b : Fin r → MvPolynomial (Ix κ) ℚ), 1 ≤ n → IsSecBasis x n b →
      ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ z ∈ pts (coordIdeal ℤ x),
        bergmanDensity μ (fun k => secFun (b k)) (wgt (interp m₀ m₁ t) n) z ≤ C * (n : ℝ) ^ D := by sorry
