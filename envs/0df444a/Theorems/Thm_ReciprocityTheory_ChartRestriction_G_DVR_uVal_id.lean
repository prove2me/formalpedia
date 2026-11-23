-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_uVal_id
-- name    : ReciprocityTheory.ChartRestriction.G.DVR.uVal_id
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T09:15:36.316807+00:00
-- url     : https://prove2.me/theorems/89f3a5ec-1d91-4f84-b7c9-af40d24dfe8e
-- title:
--   DVR: u Val id
-- statement:
--   The DVR construction uses the u Val id property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/DiscreteValuationRings/PhiGenPf.lean#L335-L338
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/DiscreteValuationRings/PhiGenPf.lean#L335-L338

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

theorem ReciprocityTheory.ChartRestriction.G.DVR.uVal_id (α : D.X) (m : TF (R := R) F ⟶ D.P.A) (y : (DegPre.BF D F).left) (J) :
    uVal D F k α m (𝟙 _) y J = cubN (th D y J) k (cP D _ α) (fst _ _ ≫ m) (DegPre.prB D F) *
      (th D y J (cP D _ α) (DegPre.prB D F) (fst _ _ ≫ m))⁻¹ := by sorry
