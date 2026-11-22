-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_spMap_comp
-- name    : ReciprocityTheory.ChartRestriction.G.Chart.spMap_comp
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T17:33:20.952052+00:00
-- url     : https://prove2.me/theorems/90175487-0e15-4066-a163-d8eaa0c0ea39
-- title:
--   Chart: sp Map comp
-- statement:
--   The Chart construction uses the sp Map comp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ExtensionDescent/ChartPullbacks/UniversalCharts/LePreimageOfNil.lean#L29-L34
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ExtensionDescent/ChartPullbacks/UniversalCharts/LePreimageOfNil.lean#L29-L34

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

theorem ReciprocityTheory.ChartRestriction.G.Chart.spMap_comp {P P' P'' : Type} [CommRing P] [Algebra R₀ P] [CommRing P'] [Algebra R₀ P']
    [CommRing P''] [Algebra R₀ P''] (g : P →ₐ[R₀] P') (g' : P' →ₐ[R₀] P'') :
    spMap g' ≫ spMap g = spMap (R₀ := R₀) (g'.comp g) := by sorry
