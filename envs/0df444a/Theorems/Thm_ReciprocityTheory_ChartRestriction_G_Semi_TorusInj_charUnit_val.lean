-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Semi_TorusInj_charUnit_val
-- name    : ReciprocityTheory.ChartRestriction.G.Semi.TorusInj.charUnit_val
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T09:19:31.761229+00:00
-- url     : https://prove2.me/theorems/555dad27-651d-4f5d-a4cf-41a300c241db
-- title:
--   Torus Inj: char Unit val
-- statement:
--   The Torus Inj construction uses the char Unit val property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ExtensionDescent/ChartPullbacks/WeightedChartPullback/TorusInj.lean#L120-L125
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ExtensionDescent/ChartPullbacks/WeightedChartPullback/TorusInj.lean#L120-L125

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

theorem ReciprocityTheory.ChartRestriction.G.Semi.TorusInj.charUnit_val (χ : X) :
    (charUnit S X χ).val = ((tFst (S := S) X).appLE ⊤ ⊤
      (tle _)).hom
      ((Scheme.ΓSpecIso (torusRing ZU X)).inv.hom (AddMonoidAlgebra.single χ 1)) := by sorry
