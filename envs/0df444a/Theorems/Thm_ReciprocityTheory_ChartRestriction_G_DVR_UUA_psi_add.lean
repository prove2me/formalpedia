-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_UUA_psi_add
-- name    : ReciprocityTheory.ChartRestriction.G.DVR.UUA.psi_add
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T11:14:27.222957+00:00
-- url     : https://prove2.me/theorems/1929e7d1-3099-4eee-9031-719f786b77ef
-- title:
--   UUA: psi add
-- statement:
--   The UUA construction uses the psi add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/DiscreteValuationRings/ValPowGen.lean#L39-L50
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/DiscreteValuationRings/ValPowGen.lean#L39-L50

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

theorem ReciprocityTheory.ChartRestriction.G.DVR.UUA.psi_add (a b : D.X) : val (D.psi (a + b)) (σ.left ≫ jFK (R := R) F) z J =
    val (D.tau a b) (σ.left ≫ jFK (R := R) F) z J * val (D.psi a) (σ.left ≫ jFK (R := R) F) z J *
      val (D.psi b) (σ.left ≫ jFK (R := R) F) z J * val D.rigK (σ.left ≫ jFK (R := R) F) z J := by sorry
