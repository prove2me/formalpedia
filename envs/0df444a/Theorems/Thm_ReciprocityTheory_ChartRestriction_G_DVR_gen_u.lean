-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_gen_u
-- name    : ReciprocityTheory.ChartRestriction.G.DVR.gen_u
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T09:15:09.187801+00:00
-- url     : https://prove2.me/theorems/45adeb85-6b4f-4117-a0db-472f2aa52d7d
-- title:
--   DVR: gen u
-- statement:
--   The DVR construction uses the gen u property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/DiscreteValuationRings/PhiGenPf.lean#L90-L159
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/DiscreteValuationRings/PhiGenPf.lean#L90-L159

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PhiGen
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PhiGenPf
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.DVR
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
variable {R : Type} [CommRing R] [IsDomain R] (D : DegPre R) (F : Type) [Field F] [Algebra (FractionRing R) F]

theorem ReciprocityTheory.ChartRestriction.G.DVR.gen_u (hG : GlobalFnsSt) (k : ℕ) (α α' : D.X) (m : TF (R := R) F ⟶ D.P.A)
    (hα : cP D _ α' = cP D _ α * m ^ k) {K : Type} [Fintype K] {φ : K → ((TF (R := R) F).left ⟶ D.P.A.left)} {ε : K → ℤ}
    (v : LB.Gen (LB.LinComb D.P.L φ ε)) (hv : v.IsGen)
    (hF : ∀ (U : Type) [CommGroup U] (h : ((TF (R := R) F).left ⟶ D.P.A.left) → U), ∏ i, h (φ i) ^ ε i =
      (h (cP D _ α * m).left)⁻¹ * h (cP D _ α).left * h m.left * (h (1 : TF (R := R) F ⟶ D.P.A).left)⁻¹ *
        (h m.left ^ k)⁻¹ * h (1 : TF (R := R) F ⟶ D.P.A).left ^ k) :
    (∃ u : LB.Gen (LB.LinComb D.P.L (Sum.elim (DegPre.famφ D F α')
        (fun i => (DegPre.trPt D F m).left ≫ DegPre.famφ D F α i)) (DegPre.deltaε k)), u.IsGen ∧
      LB.Gen.Corr D.P.L _ _ _ _ (LB.pullGen D.P.L _ _ u (DegPre.zF D F).left) v) ∧
    ∀ u : LB.Gen (LB.LinComb D.P.L (Sum.elim (DegPre.famφ D F α')
        (fun i => (DegPre.trPt D F m).left ≫ DegPre.famφ D F α i)) (DegPre.deltaε k)), u.IsGen →
      LB.Gen.Corr D.P.L _ _ _ _ (LB.pullGen D.P.L _ _ u (DegPre.zF D F).left) v →
      ∀ (T : Over (Spec (CommRingCat.of R))) (ρ : T ⟶ DegPre.BF D F) (z : T.left) (J), Good D.P.L z J →
        val u ρ.left z J = uVal D F k α m ρ z J * val v (ρ ≫ fst _ _).left z J := by sorry
