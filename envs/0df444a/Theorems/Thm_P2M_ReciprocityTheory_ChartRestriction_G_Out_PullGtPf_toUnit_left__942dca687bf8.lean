-- Prove2me | Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_Out_PullGtPf_toUnit_left__942dca687bf8
-- name    : P2M_ReciprocityTheory_ChartRestriction_G_Out_PullGtPf_toUnit_left__942dca687bf8
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T15:24:54.099205+00:00
-- url     : https://prove2.me/theorems/4e155168-e713-41ab-b621-245dd1624262
-- title:
--   P2 M Reciprocity Theory Chart Restriction G Out Pull Gt Pf to Unit left  942dca687bf8: P2 M Reciprocity Theory Chart Restriction G Out Pull Gt Pf to Unit left  942dca687bf8
-- statement:
--   The P2 M Reciprocity Theory Chart Restriction G Out Pull Gt Pf to Unit left  942dca687bf8 construction uses the P2 M Reciprocity Theory Chart Restriction G Out Pull Gt Pf to Unit left  942dca687bf8 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ExtensionDescent/ChartPullbacks/UniformBaseChange/PullGt.lean#L304-L307
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ExtensionDescent/ChartPullbacks/UniformBaseChange/PullGt.lean#L304-L307

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_UniformBaseChange_PullGtSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_BCTools
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SabComp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_WeightedChartPullback_TorusInj
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_UniformBaseChange_PullGt
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
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj
  AlgebraicGeometry
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Out.PullGtPf
open Semi Geo.Tor
variable {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] {I : Ideal R}
  {I' : Ideal R'} (φ : R →+* R') (hφ : I.map φ ≤ I') (e : ℕ)
variable {φ hφ e}

theorem P2M_ReciprocityTheory_ChartRestriction_G_Out_PullGtPf_toUnit_left__942dca687bf8 {S : Scheme.{0}} (Z : Over S) : (toUnit Z).left = Z.hom := by sorry

alias «ReciprocityTheory».«ChartRestriction».«G».«Out».«PullGtPf».«toUnit_left'» := P2M_ReciprocityTheory_ChartRestriction_G_Out_PullGtPf_toUnit_left__942dca687bf8
