-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_TWO_lift_unique
-- name    : ReciprocityTheory.ChartRestriction.G.DVR.TWO.lift_unique
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T10:12:44.620241+00:00
-- url     : https://prove2.me/theorems/61c61b47-79b0-5299-a50f-04a68029c7bc
-- title:
--   TWO: lift unique
-- statement:
--   The TWO construction uses the lift unique property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/DiscreteValuationRings/ExistsWeightBasisFiltration.lean#L125-L136
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/DiscreteValuationRings/ExistsWeightBasisFiltration.lean#L125-L136

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_ValuationMultiplicationInvariance
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_LBLocalC
import Mathlib.AlgebraicGeometry.ValuativeCriterion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_ExistsWeightBasisFiltration
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
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.TWO
open ReciprocityTheory.ChartRestriction.G.Out
variable {F : Type} [Field F] (v : AddValuation F (WithTop ℚ))
variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] {ϖ : V}
  [Algebra (FractionRing V) F]

theorem ReciprocityTheory.ChartRestriction.G.DVR.TWO.lift_unique (hϖ : Irreducible ϖ) (hv : ValOver ϖ F v) {X : Scheme.{0}} (p : X ⟶ Spec (CommRingCat.of V))
    [IsSeparated p] (x₁ x₂ : Spec (CommRingCat.of (Ov v)) ⟶ X)
    (h₁ : x₁ ≫ p = Spec.map (CommRingCat.ofHom (fO v hϖ hv))) (h₂ : x₂ ≫ p = Spec.map (CommRingCat.ofHom (fO v hϖ hv)))
    (h : Spec.map (CommRingCat.ofHom (algebraMap (Ov v) F)) ≫ x₁ = Spec.map (CommRingCat.ofHom (algebraMap (Ov v) F)) ≫ x₂) :
    x₁ = x₂ := by sorry
