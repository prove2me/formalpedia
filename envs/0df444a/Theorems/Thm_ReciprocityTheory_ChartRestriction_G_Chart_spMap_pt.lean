-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_spMap_pt
-- name    : ReciprocityTheory.ChartRestriction.G.Chart.spMap_pt
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T09:14:08.261073+00:00
-- url     : https://prove2.me/theorems/276a7580-c3cb-4a25-9f36-e62e816ac004
-- title:
--   Chart: sp Map pt
-- statement:
--   The Chart construction uses the sp Map pt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ExtensionDescent/ChartPullbacks/UniversalCharts/LePreimageOfNil.lean#L68-L72
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ExtensionDescent/ChartPullbacks/UniversalCharts/LePreimageOfNil.lean#L68-L72

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

theorem ReciprocityTheory.ChartRestriction.G.Chart.spMap_pt (C : Chart G) {P P' : Type} [CommRing P] [Algebra R₀ P] [CommRing P'] [Algebra R₀ P']
    (g : P →ₐ[R₀] P') (h : Γ(G.left, C.U) →ₐ[R₀] P) : spMap g ≫ pt C h = pt C (g.comp h) := by sorry
