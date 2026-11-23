-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_le_preimage_of_nil
-- name    : ReciprocityTheory.ChartRestriction.G.Chart.le_preimage_of_nil
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T09:14:44.693384+00:00
-- url     : https://prove2.me/theorems/c72f9cfa-46ec-4e60-aa8b-637f88a6779b
-- title:
--   Chart: le preimage of nil
-- statement:
--   The Chart construction uses the le preimage of nil property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ExtensionDescent/ChartPullbacks/UniversalCharts/LePreimageOfNil.lean#L109-L140
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ExtensionDescent/ChartPullbacks/UniversalCharts/LePreimageOfNil.lean#L109-L140

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

theorem ReciprocityTheory.ChartRestriction.G.Chart.le_preimage_of_nil (C : Chart G) {P P₀ : Type} [CommRing P] [Algebra R₀ P] [CommRing P₀]
    [Algebra R₀ P₀] (q : P →ₐ[R₀] P₀) (hq : Function.Surjective q)
    (hn : ∀ a ∈ RingHom.ker q, IsNilpotent a) (x : sp P ⟶ G) (h₀ : Γ(G.left, C.U) →ₐ[R₀] P₀)
    (hx : spMap q ≫ x = pt C h₀) : ⊤ ≤ x.left ⁻¹ᵁ C.U := by sorry
