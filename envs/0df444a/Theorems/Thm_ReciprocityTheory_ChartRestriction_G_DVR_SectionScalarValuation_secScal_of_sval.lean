-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_SectionScalarValuation_secScal_of_sval
-- name    : ReciprocityTheory.ChartRestriction.G.DVR.SectionScalarValuation.secScal_of_sval
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T09:15:01.191811+00:00
-- url     : https://prove2.me/theorems/9e02c189-45a3-4127-bc76-a0bb79755e28
-- title:
--   Section Scalar Valuation: sec Scal of sval
-- statement:
--   The Section Scalar Valuation construction uses the sec Scal of sval property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/DiscreteValuationRings/SectionScalarValuation.lean#L62-L78
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/DiscreteValuationRings/SectionScalarValuation.lean#L62-L78

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_GenCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_AppCompatGeneric
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_SectionScalarValuation
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
  CartesianMonoidalCategory MonObj
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.SectionScalarValuation
open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor IsLocalRing
variable {X Y Y' Z : Scheme.{0}} {L : LB X} {K₁ K₂ : Type} [Fintype K₁] [Fintype K₂]

theorem ReciprocityTheory.ChartRestriction.G.DVR.SectionScalarValuation.secScal_of_sval (hL : L.IsLB) {φ₁ : K₁ → (Y' ⟶ X)} {ε₁ : K₁ → ℤ}
    {s₁ : LB.Sec (LB.LinComb L φ₁ ε₁)} {φ₂ : K₂ → (Y ⟶ X)} {ε₂ : K₂ → ℤ}
    {s₂ : LB.Sec (LB.LinComb L φ₂ ε₂)} {h : Y' ⟶ Y}
    (H : ∀ (y : Y') (J : (Y' ⟶ X) → L.ι), Good L y J → sval s₂ (𝟙 Y' ≫ h) y J = sval s₁ (𝟙 Y') y J) :
    GeneratorPullback.SecScal L φ₁ ε₁ s₁ φ₂ ε₂ s₂ h 1 := by sorry
