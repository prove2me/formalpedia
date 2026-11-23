-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Out_PullGtPf_isMonHom_of_grpPullback
-- name    : ReciprocityTheory.ChartRestriction.G.Out.PullGtPf.isMonHom_of_grpPullback
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T14:42:53.836832+00:00
-- url     : https://prove2.me/theorems/879ac8fb-83c4-454e-a08d-39dc10148f17
-- title:
--   Pull Gt Pf: is Mon Hom of grp Pullback
-- statement:
--   The Pull Gt Pf construction uses the is Mon Hom of grp Pullback property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ExtensionDescent/ChartPullbacks/UniformBaseChange/PullGt.lean#L107-L131
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ExtensionDescent/ChartPullbacks/UniformBaseChange/PullGt.lean#L107-L131

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
variable {S S' : Scheme.{0}} {f : S' ⟶ S}

theorem ReciprocityTheory.ChartRestriction.G.Out.PullGtPf.isMonHom_of_grpPullback {G B : Over S} [GrpObj G] [GrpObj B] {G' B' : Over S'} [GrpObj G']
    [GrpObj B'] {φG : G'.left ⟶ G.left} {φB : B'.left ⟶ B.left} (hG : IsGrpPullback G' G f φG)
    (hB : IsGrpPullback B' B f φB) (q : G ⟶ B) [IsMonHom q] (q' : G' ⟶ B')
    (hq : q'.left ≫ φB = φG ≫ q.left) : IsMonHom q' := by sorry
