-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_exists_pt
-- name    : ReciprocityTheory.ChartRestriction.G.Chart.exists_pt
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T09:15:10.906985+00:00
-- url     : https://prove2.me/theorems/2f4f7666-e2a8-4028-978c-04ef521e75f0
-- title:
--   Chart: exists pt
-- statement:
--   The Chart construction uses the exists pt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ExtensionDescent/ChartPullbacks/UniversalCharts/LePreimageOfNil.lean#L91-L107
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ExtensionDescent/ChartPullbacks/UniversalCharts/LePreimageOfNil.lean#L91-L107

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_UniversalCharts_LePreimageOfNil
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Chart
attribute [local instance] Over.cartesianMonoidalCategory
variable {R₀ : Type} [CommRing R₀]
variable (G : Over (Spec (CommRingCat.of R₀))) [GrpObj G]
variable {G}

theorem ReciprocityTheory.ChartRestriction.G.Chart.exists_pt (C : Chart G) {P : Type} [CommRing P] [Algebra R₀ P] (x : sp P ⟶ G)
    (hx : ⊤ ≤ x.left ⁻¹ᵁ C.U) : ∃ h : Γ(G.left, C.U) →ₐ[R₀] P, x = pt C h := by sorry
