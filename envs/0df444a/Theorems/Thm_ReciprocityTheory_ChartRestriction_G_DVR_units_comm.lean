-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_units_comm
-- name    : ReciprocityTheory.ChartRestriction.G.DVR.units_comm
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T10:13:54.866252+00:00
-- url     : https://prove2.me/theorems/002c254d-7c99-53f7-b9a0-cd0844db1793
-- title:
--   DVR: units comm
-- statement:
--   The DVR construction uses the units comm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/DiscreteValuationRings/PhiGenPf.lean#L359-L382
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/DiscreteValuationRings/PhiGenPf.lean#L359-L382

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

theorem ReciprocityTheory.ChartRestriction.G.DVR.units_comm (hB : D.TauBimult) (mu α : D.X) (y : (DegPre.BF D F).left) {J} (hJ : Good D.P.L y J) :
    uVal D F k α (cP D _ mu) (DegPre.trPt D F p.g.b) y J *
        val (DegPre.famMult D F k mu α) (fst (TF (R := R) F) D.P.A).left y J *
      (uVal D F k (α + k • mu) p.g.b (𝟙 _) y J *
        val (LB.mulGen D.P.L _ _ _ _ (p.g.s (α + k • mu)) w) (fst (TF (R := R) F) D.P.A).left y J) =
    uVal D F k α p.g.b (DegPre.trPt D F (cP D _ mu)) y J *
        val (LB.mulGen D.P.L _ _ _ _ (p.g.s α) w) (fst (TF (R := R) F) D.P.A).left y J *
      (uVal D F k (α + p.y) (cP D _ mu) (𝟙 _) y J *
        val (DegPre.famMult D F k mu (α + p.y)) (fst (TF (R := R) F) D.P.A).left y J) := by sorry
