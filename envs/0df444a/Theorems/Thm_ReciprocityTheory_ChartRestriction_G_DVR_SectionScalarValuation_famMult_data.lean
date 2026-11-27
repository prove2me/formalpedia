-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_SectionScalarValuation_famMult_data
-- name    : ReciprocityTheory.ChartRestriction.G.DVR.SectionScalarValuation.famMult_data
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-27T06:22:57.948342+00:00
-- url     : https://prove2.me/theorems/e1d63495-a48b-5b02-8bd0-0e96961a4ba4
-- title:
--   Section Scalar Valuation: fam Mult data
-- statement:
--   The Section Scalar Valuation construction uses the fam Mult data property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/DiscreteValuationRings/ExistsValGenHasVal.lean#L95-L132
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/DiscreteValuationRings/ExistsValGenHasVal.lean#L95-L132

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_ProdNeg
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_ExistsRosatiGen
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_ExistsValGenHasVal
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
open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor IsLocalRing QForm
variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] {ϖ : V}
  (D : DegData V (maximalIdeal V)) {Q : D.toPre.X → ℤ}

theorem ReciprocityTheory.ChartRestriction.G.DVR.SectionScalarValuation.famMult_data (hϖ : Irreducible ϖ) (hQ : IsQ D.toPre ϖ Q) (k : ℕ) (mu α : D.toPre.X) :
    ∃ (Ix : Type) (_ : Fintype Ix) (φV : Ix → (Spec (CommRingCat.of V) ⟶ D.toPre.P.A.left)) (εV : Ix → ℤ)
      (e' : LB.Gen (LB.LinComb D.toPre.P.L φV εV)), e'.IsGen ∧
      (∀ (U : Type) [CommGroup U] (h : (D.toPre.P.A.left ⟶ D.toPre.P.A.left) → U),
        ∏ i, h (D.toPre.P.A.hom ≫ φV i) ^ εV i =
          (h (cQ D.toPre D.toPre.P.A α * cQ D.toPre D.toPre.P.A mu).left)⁻¹ * h (cQ D.toPre D.toPre.P.A α).left *
            h (cQ D.toPre D.toPre.P.A mu).left * (h (1 : D.toPre.P.A ⟶ D.toPre.P.A).left)⁻¹ *
            (h (cQ D.toPre D.toPre.P.A mu).left ^ k)⁻¹ * h (1 : D.toPre.P.A ⟶ D.toPre.P.A).left ^ k) ∧
      ∃ c₀ : FractionRing V, HasVal ϖ c₀ (k * Q mu + bOf D.toPre Q mu α) ∧
        ∀ (F : Type) [Field F] [Algebra (FractionRing V) F] (Z : Scheme.{0}) (r : Z ⟶ Spec (CommRingCat.of F))
          (z : Z) (J : (Z ⟶ D.toPre.P.A.left) → D.toPre.P.L.ι), Good D.toPre.P.L z J →
          (val (DegPre.famMult D.toPre F k mu α) r z J).val =
            gs (r ≫ jFK (R := V) F) z ⊤ (scal (𝟙 _) c₀) * (val e' (r ≫ DegPre.jFR (R := V) F) z J).val := by sorry
