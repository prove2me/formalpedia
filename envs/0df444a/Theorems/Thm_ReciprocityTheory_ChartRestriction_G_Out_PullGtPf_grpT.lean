-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Out_PullGtPf_grpT
-- name    : ReciprocityTheory.ChartRestriction.G.Out.PullGtPf.grpT
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T14:41:35.609152+00:00
-- url     : https://prove2.me/theorems/32d41c7a-f974-43ce-8ca2-1cb0859a8a1d
-- title:
--   Pull Gt Pf: grp T
-- statement:
--   The Pull Gt Pf construction uses the grp T property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ExtensionDescent/ChartPullbacks/UniformBaseChange/PullGt.lean#L248-L255
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ExtensionDescent/ChartPullbacks/UniformBaseChange/PullGt.lean#L248-L255

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
variable (hφ e) {X X' : Type} [AddCommGroup X] [AddCommGroup X'] (xe : X' ≃+ X)

theorem ReciprocityTheory.ChartRestriction.G.Out.PullGtPf.grpT : IsGrpPullback (splitTorus (Spec (CommRingCat.of (R' ⧸ I' ^ (e + 1)))) X')
    (splitTorus (Spec (CommRingCat.of (R ⧸ I ^ (e + 1)))) X) (sE φ hφ e) (hT hφ e xe) := by sorry
