-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_uVal_tr
-- name    : ReciprocityTheory.ChartRestriction.G.DVR.uVal_tr
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T12:25:14.359474+00:00
-- url     : https://prove2.me/theorems/f843b61f-595c-4c08-b023-57d9d47ac3af
-- title:
--   DVR: u Val tr
-- statement:
--   The DVR construction uses the u Val tr property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/DiscreteValuationRings/PhiGenPf.lean#L341-L346
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/DiscreteValuationRings/PhiGenPf.lean#L341-L346

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
variable (hG : GlobalFnsSt) {k : ℕ} (p : QkPt D F k)
  (w : LB.Gen (LB.LinComb D.P.L (DegPre.lineφ D F p.g.b) (DegPre.lineε k))) (hw : w.IsGen)
include hG hw
omit hG hw

theorem ReciprocityTheory.ChartRestriction.G.DVR.uVal_tr (α : D.X) (m m' : TF (R := R) F ⟶ D.P.A) (y : (DegPre.BF D F).left) (J) :
    uVal D F k α m (DegPre.trPt D F m') y J =
      cubN (th D y J) k (cP D _ α) (fst _ _ ≫ m) (DegPre.prB D F * (fst _ _ ≫ m')) *
        (th D y J (cP D _ α) (DegPre.prB D F * (fst _ _ ≫ m')) (fst _ _ ≫ m))⁻¹ := by sorry
