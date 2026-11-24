-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AI_I2_IsIntersectionFamily_isRFamily
-- name    : ReciprocityTheory.ChartRestriction.G.AI.I2.IsIntersectionFamily.isRFamily
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T06:06:54.554403+00:00
-- url     : https://prove2.me/theorems/3aec642d-7632-4899-a978-244520392fda
-- title:
--   Is Intersection Family: is RFamily
-- statement:
--   The Is Intersection Family construction uses the is RFamily property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArithmeticIntersection/RationalSections/IsRatSectionOn.lean#L28-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArithmeticIntersection/RationalSections/IsRatSectionOn.lean#L28-L30

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_RationalSections_IsRatSectionOn
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.AI ReciprocityTheory.ChartRestriction.G.AI.I2
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]

theorem ReciprocityTheory.ChartRestriction.G.AI.I2.IsIntersectionFamily.isRFamily {I : Ideal (MRing ι) → (n : ℕ) → (Fin n → HermLine ι) → ℝ}
    (h : IsIntersectionFamily I) : IsRFamily I := by sorry
