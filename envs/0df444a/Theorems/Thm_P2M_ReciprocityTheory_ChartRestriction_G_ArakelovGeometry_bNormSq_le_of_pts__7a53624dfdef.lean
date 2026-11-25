-- Prove2me | Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_bNormSq_le_of_pts__7a53624dfdef
-- name    : P2M_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_bNormSq_le_of_pts__7a53624dfdef
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T16:00:40.492434+00:00
-- url     : https://prove2.me/theorems/e08b2320-1d1d-477e-a339-b7cda04f5bef
-- title:
--   P2 M Reciprocity Theory Chart Restriction G Arakelov Geometry b Norm Sq le of pts  7a53624dfdef: P2 M Reciprocity Theory Chart Restriction G Arakelov Geometry b Norm Sq le of pts  7a53624dfdef
-- statement:
--   The P2 M Reciprocity Theory Chart Restriction G Arakelov Geometry b Norm Sq le of pts  7a53624dfdef construction uses the P2 M Reciprocity Theory Chart Restriction G Arakelov Geometry b Norm Sq le of pts  7a53624dfdef property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovGeometry/CSandwichStE.lean#L35-L46
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovGeometry/CSandwichStE.lean#L35-L46

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_CSandwichStD
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_CSandwichStE
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
open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.GeometryOfNumbersTheory MvPolynomial MeasureTheory Module Filter Asymptotics
open scoped ComplexOrder Matrix
variable {Ω : Type} [Field Ω] [CharZero Ω] {κ : Type} [Fintype κ] {D : ℕ}

theorem P2M_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_bNormSq_le_of_pts__7a53624dfdef {x : Ix κ → Ω} {m : ConeMetric ℂ (Ix κ)} {μ : Measure (Ix κ → ℂ)}
    (hg : IsGood D x m μ) {n r : ℕ} (s : Fin r → (Ix κ → ℂ) → ℂ) (c : Fin r → ℂ) {B : ℝ}
    (h : ∀ z ∈ pts (coordIdeal ℤ x), ‖∑ j, c j * s j z‖ ^ 2 * wgt m n z ≤ B) :
    bNormSq μ s (wgt m n) c ≤ B := by sorry

alias «ReciprocityTheory».«ChartRestriction».«G».«ArakelovGeometry».«bNormSq_le_of_pts'» := P2M_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_bNormSq_le_of_pts__7a53624dfdef
