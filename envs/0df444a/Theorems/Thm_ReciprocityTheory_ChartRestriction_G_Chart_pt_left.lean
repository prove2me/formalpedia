-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_pt_left
-- name    : ReciprocityTheory.ChartRestriction.G.Chart.pt_left
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T17:31:09.829848+00:00
-- url     : https://prove2.me/theorems/597bd19b-8772-4f50-9978-70e367ae67f4
-- title:
--   Chart: pt left
-- statement:
--   The Chart construction uses the pt left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ExtensionDescent/ChartPullbacks/UniversalCharts/LePreimageOfNil.lean#L65-L66
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ExtensionDescent/ChartPullbacks/UniversalCharts/LePreimageOfNil.lean#L65-L66

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

theorem ReciprocityTheory.ChartRestriction.G.Chart.pt_left (C : Chart G) {P : Type} [CommRing P] [Algebra R₀ P] (h : Γ(G.left, C.U) →ₐ[R₀] P) :
    (pt C h).left = Spec.map (CommRingCat.ofHom h.toRingHom) ≫ C.hU.fromSpec := by sorry
