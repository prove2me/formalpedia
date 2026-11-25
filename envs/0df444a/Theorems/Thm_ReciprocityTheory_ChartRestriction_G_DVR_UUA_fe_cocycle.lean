-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_UUA_fe_cocycle
-- name    : ReciprocityTheory.ChartRestriction.G.DVR.UUA.fe_cocycle
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T10:17:46.805061+00:00
-- url     : https://prove2.me/theorems/058da495-149b-5426-ab41-cc23cc614263
-- title:
--   UUA: fe cocycle
-- statement:
--   The UUA construction uses the fe cocycle property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/DiscreteValuationRings/ValPowGen.lean#L59-L108
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/DiscreteValuationRings/ValPowGen.lean#L59-L108

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_CubicNormMulIdentity
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PhiGenPf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_ValPowGen
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
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.UUA
open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.H1
variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {F : Type} [Field F] [Algebra (FractionRing R) F]

theorem ReciprocityTheory.ChartRestriction.G.DVR.UUA.fe_cocycle (hB : D.TauBimult) {T : Over (Spec (CommRingCat.of R))} (ρ' : T ⟶ DegPre.BF D F) {z : T.left}
    {J : (T.left ⟶ D.P.A.left) → D.P.L.ι} (hJ : Good D.P.L z J) (k : ℕ) (ρ mu nu : D.X) :
    (uVal D F k ρ (cP D _ mu) (ρ' ≫ DegPre.trF D F nu) z J *
        val (DegPre.famMult D F k mu ρ) (ρ' ≫ fst _ _).left z J) *
      (uVal D F k (ρ + k • mu) (cP D _ nu) ρ' z J * val (DegPre.famMult D F k nu (ρ + k • mu)) (ρ' ≫ fst _ _).left z J) =
    uVal D F k ρ (cP D _ (mu + nu)) ρ' z J * val (DegPre.famMult D F k (mu + nu) ρ) (ρ' ≫ fst _ _).left z J := by sorry
