-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_val_famMult
-- name    : ReciprocityTheory.ChartRestriction.G.DVR.val_famMult
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T09:15:46.313153+00:00
-- url     : https://prove2.me/theorems/ba90771d-c692-485c-99e7-94a5427a3a9d
-- title:
--   DVR: val fam Mult
-- statement:
--   The DVR construction uses the val fam Mult property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/DiscreteValuationRings/PhiGenPf.lean#L305-L310
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/DiscreteValuationRings/PhiGenPf.lean#L305-L310

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
variable {D F}

theorem ReciprocityTheory.ChartRestriction.G.DVR.val_famMult {T : Over (Spec (CommRingCat.of R))} (σ : T ⟶ TF (R := R) F) {z : T.left}
    {J : (T.left ⟶ D.P.A.left) → D.P.L.ι} (hJ : Good D.P.L z J) (k : ℕ) (mu α : D.X) :
    val (DegPre.famMult D F k mu α) σ.left z J = val (D.tau mu α) (σ.left ≫ jFK (R := R) F) z J *
      (val (GeneratorPullback.powGen D.P.L _ _ (D.psi mu) k) (σ.left ≫ jFK (R := R) F) z J *
        val (GeneratorPullback.powGen D.P.L _ _ D.rigK k) (σ.left ≫ jFK (R := R) F) z J) := by sorry
