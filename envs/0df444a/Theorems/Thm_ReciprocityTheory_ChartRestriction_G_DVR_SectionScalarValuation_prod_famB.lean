-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_SectionScalarValuation_prod_famB
-- name    : ReciprocityTheory.ChartRestriction.G.DVR.SectionScalarValuation.prod_famB
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T11:11:40.542705+00:00
-- url     : https://prove2.me/theorems/afe2d435-0164-436b-938a-2223cd058685
-- title:
--   Section Scalar Valuation: prod fam B
-- statement:
--   The Section Scalar Valuation construction uses the prod fam B property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/DiscreteValuationRings/ProdNeg.lean#L39-L54
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/DiscreteValuationRings/ProdNeg.lean#L39-L54

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_SectionScalarValuation
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_ProdNeg
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
open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
variable {R : Type} [CommRing R] [IsDomain R] (D : DegPre R)

theorem ReciprocityTheory.ChartRestriction.G.DVR.SectionScalarValuation.prod_famB {T : Over (Spec (CommRingCat.of R))} (ρ : T ⟶ D.P.A) (χ : D.X) (k : ℕ) {U : Type} [CommGroup U]
    (h : (T.left ⟶ D.P.A.left) → U) : ∏ i, h (ρ.left ≫ D.famφB χ i) ^ DegPre.famε k i =
      h ρ.left ^ ((k : ℤ) - 1) * h (ρ * cQ D T χ).left * (h (cQ D T χ).left)⁻¹ * h (1 : T ⟶ D.P.A).left := by sorry
