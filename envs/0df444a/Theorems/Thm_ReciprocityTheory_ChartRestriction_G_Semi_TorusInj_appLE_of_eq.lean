-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Semi_TorusInj_appLE_of_eq
-- name    : ReciprocityTheory.ChartRestriction.G.Semi.TorusInj.appLE_of_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T09:19:17.352596+00:00
-- url     : https://prove2.me/theorems/895777ec-ab5c-4ad7-955d-09f9acb0f8ef
-- title:
--   Torus Inj: app LE of eq
-- statement:
--   The Torus Inj construction uses the app LE of eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ExtensionDescent/ChartPullbacks/WeightedChartPullback/TorusInj.lean#L80-L83
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ExtensionDescent/ChartPullbacks/WeightedChartPullback/TorusInj.lean#L80-L83

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

theorem ReciprocityTheory.ChartRestriction.G.Semi.TorusInj.appLE_of_eq {A B : Scheme.{0}} {f g : A ⟶ B} (hfg : f = g) {U : B.Opens} {W : A.Opens}
    (e : W ≤ f ⁻¹ᵁ U) : f.appLE U W e = g.appLE U W (hfg ▸ e) := by sorry
