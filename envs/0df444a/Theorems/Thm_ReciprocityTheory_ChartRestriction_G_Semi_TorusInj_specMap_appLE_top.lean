-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Semi_TorusInj_specMap_appLE_top
-- name    : ReciprocityTheory.ChartRestriction.G.Semi.TorusInj.specMap_appLE_top
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T09:19:39.029651+00:00
-- url     : https://prove2.me/theorems/9f2300cf-9d80-4369-a6a0-4e190aee5d4e
-- title:
--   Torus Inj: spec Map app LE top
-- statement:
--   The Torus Inj construction uses the spec Map app LE top property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ExtensionDescent/ChartPullbacks/WeightedChartPullback/TorusInj.lean#L85-L94
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ExtensionDescent/ChartPullbacks/WeightedChartPullback/TorusInj.lean#L85-L94

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_AbelianSchemeQuotients_QSurjective
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_WeightedChartPullback_TorusInj
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
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
  CartesianMonoidalCategory
open scoped AlgebraMonoidAlgebra
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Semi.TorusInj
variable {S : Scheme.{0}} (X : Type) [AddCommGroup X] (Y : Over S)
variable {X Y} {V : Y.left.Opens} (hV : IsAffineOpen V)
attribute [local instance] zuAlg

theorem ReciprocityTheory.ChartRestriction.G.Semi.TorusInj.specMap_appLE_top {R R' : CommRingCat.{0}} (f : R ⟶ R') (e) :
    (Scheme.ΓSpecIso R).inv ≫ (Spec.map f).appLE ⊤ ⊤ e ≫ (Scheme.ΓSpecIso R').hom = f := by sorry
