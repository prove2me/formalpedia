-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_UUA_tau_nsmul
-- name    : ReciprocityTheory.ChartRestriction.G.DVR.UUA.tau_nsmul
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T10:16:55.48227+00:00
-- url     : https://prove2.me/theorems/072322c6-4b08-4996-9fc2-a319e120caa3
-- title:
--   UUA: tau nsmul
-- statement:
--   The UUA construction uses the tau nsmul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/DiscreteValuationRings/ValPowGen.lean#L24-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/DiscreteValuationRings/ValPowGen.lean#L24-L37

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
variable {T : Over (Spec (CommRingCat.of R))} (σ : T ⟶ TF (R := R) F) {z : T.left}
  {J : (T.left ⟶ D.P.A.left) → D.P.L.ι} (hJ : Good D.P.L z J)
include hJ

theorem ReciprocityTheory.ChartRestriction.G.DVR.UUA.tau_nsmul (hB : D.TauBimult) (ρ mu nu : D.X) (k : ℕ) :
    val (D.tau (ρ + k • mu) nu) (σ.left ≫ jFK (R := R) F) z J * cubN (th D z J) k (cP D T ρ) (cP D T mu) (cP D T nu) =
      val (D.tau ρ nu) (σ.left ≫ jFK (R := R) F) z J * val (D.tau mu nu) (σ.left ≫ jFK (R := R) F) z J ^ k := by sorry
