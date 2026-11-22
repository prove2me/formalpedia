-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_spMap_left
-- name    : ReciprocityTheory.ChartRestriction.G.Chart.spMap_left
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T17:30:55.541883+00:00
-- url     : https://prove2.me/theorems/d3a83346-859c-4083-b92f-46831e4d4127
-- title:
--   Chart: sp Map left
-- statement:
--   The Chart construction uses the sp Map left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ExtensionDescent/ChartPullbacks/UniversalCharts/LePreimageOfNil.lean#L26-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ExtensionDescent/ChartPullbacks/UniversalCharts/LePreimageOfNil.lean#L26-L27

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

theorem ReciprocityTheory.ChartRestriction.G.Chart.spMap_left {P P' : Type} [CommRing P] [Algebra R₀ P] [CommRing P'] [Algebra R₀ P'] (g : P →ₐ[R₀] P') :
    (spMap g).left = Spec.map (CommRingCat.ofHom g.toRingHom) := by sorry
