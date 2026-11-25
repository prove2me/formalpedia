-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_TWM_gen_uO
-- name    : ReciprocityTheory.ChartRestriction.G.DVR.TWM.gen_uO
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:39:05.378889+00:00
-- url     : https://prove2.me/theorems/d4c7d997-a29d-441a-bbc0-c45f5c1f808b
-- title:
--   TWM: gen u O
-- statement:
--   The TWM construction uses the gen u O property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/DiscreteValuationRings/LiftOUnique.lean#L78-L139
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/DiscreteValuationRings/LiftOUnique.lean#L78-L139

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_TWMove
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PhiGenPf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_ProdNeg
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_LiftOUnique
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
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.TWM
open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor IsLocalRing TWO SectionScalarValuation
variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] {ϖ : V} (hϖ : Irreducible ϖ)
  {D : DegData V (maximalIdeal V)} {F : Type} [Field F] [Algebra (FractionRing V) F]
  {v : AddValuation F (WithTop ℚ)} (hv : ValOver ϖ F v)

theorem ReciprocityTheory.ChartRestriction.G.DVR.TWM.gen_uO (k : ℕ) (α α' : D.toPre.X) (m : TO hϖ hv ⟶ D.toPre.P.A)
    (hα : cP D.toPre _ α' = cP D.toPre _ α * m ^ k) {K : Type} [Fintype K]
    {φ : K → ((TO hϖ hv).left ⟶ D.toPre.P.A.left)} {ε : K → ℤ}
    (vO : LB.Gen (LB.LinComb D.toPre.P.L φ ε)) (hvO : vO.IsGen)
    (hF : ∀ (U : Type) [CommGroup U] (h : ((TO hϖ hv).left ⟶ D.toPre.P.A.left) → U), ∏ i, h (φ i) ^ ε i =
      (h (cP D.toPre _ α * m).left)⁻¹ * h (cP D.toPre _ α).left * h m.left * (h (1 : TO hϖ hv ⟶ D.toPre.P.A).left)⁻¹ *
        (h m.left ^ k)⁻¹ * h (1 : TO hϖ hv ⟶ D.toPre.P.A).left ^ k) :
    ∃ u : LB.Gen (LB.LinComb D.toPre.P.L (Sum.elim (fun i => (snd (TO hϖ hv) D.toPre.P.A).left ≫ D.toPre.famφB α' i)
        (fun i => (trO hϖ hv m ≫ snd _ _).left ≫ D.toPre.famφB α i)) (DegPre.deltaε k)), u.IsGen ∧
      ∀ (T : Over (Spec (CommRingCat.of V))) (ρ : T ⟶ TO hϖ hv ⊗ D.toPre.P.A) (z : T.left) (J), Good D.toPre.P.L z J →
        val u ρ.left z J = cubN (th D.toPre z J) k (cP D.toPre T α) (ρ ≫ fst _ _ ≫ m) (ρ ≫ snd _ _) *
          (th D.toPre z J (cP D.toPre T α) (ρ ≫ snd _ _) (ρ ≫ fst _ _ ≫ m))⁻¹ * val vO (ρ ≫ fst _ _).left z J := by sorry
