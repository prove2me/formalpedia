-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Semi_TorusInj_eq_zero_of_sum
-- name    : ReciprocityTheory.ChartRestriction.G.Semi.TorusInj.eq_zero_of_sum
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T10:57:02.371833+00:00
-- url     : https://prove2.me/theorems/32e85abd-a930-44d8-ab1d-d1cd356c351c
-- title:
--   Torus Inj: eq zero of sum
-- statement:
--   The Torus Inj construction uses the eq zero of sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ExtensionDescent/ChartPullbacks/WeightedChartPullback/TorusInj.lean#L162-L192
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ExtensionDescent/ChartPullbacks/WeightedChartPullback/TorusInj.lean#L162-L192

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

theorem ReciprocityTheory.ChartRestriction.G.Semi.TorusInj.eq_zero_of_sum {V : Y.left.Opens} (s : Finset X) (h : X → Γ(Y.left, V))
    (hs : ∑ χ ∈ s, ((splitTorus S X ⊗ Y).left.presheaf.map (homOfLE le_top).op).hom (chiP X Y χ) *
      ((snd (splitTorus S X) Y).left.app V).hom (h χ) = 0) :
    ∀ χ ∈ s, h χ = 0 := by sorry
