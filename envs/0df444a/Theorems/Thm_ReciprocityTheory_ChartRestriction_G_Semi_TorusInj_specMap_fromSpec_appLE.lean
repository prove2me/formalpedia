-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Semi_TorusInj_specMap_fromSpec_appLE
-- name    : ReciprocityTheory.ChartRestriction.G.Semi.TorusInj.specMap_fromSpec_appLE
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T10:35:10.290626+00:00
-- url     : https://prove2.me/theorems/cbc16da2-8b15-450e-b196-fe79e9dec7ed
-- title:
--   Torus Inj: spec Map from Spec app LE
-- statement:
--   The Torus Inj construction uses the spec Map from Spec app LE property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ExtensionDescent/ChartPullbacks/WeightedChartPullback/TorusInj.lean#L96-L106
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ExtensionDescent/ChartPullbacks/WeightedChartPullback/TorusInj.lean#L96-L106

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

theorem ReciprocityTheory.ChartRestriction.G.Semi.TorusInj.specMap_fromSpec_appLE {R : CommRingCat.{0}} (f : Γ(Y.left, V) ⟶ R) (e) :
    (Spec.map f ≫ hV.fromSpec).appLE V ⊤ e ≫ (Scheme.ΓSpecIso R).hom = f := by sorry
