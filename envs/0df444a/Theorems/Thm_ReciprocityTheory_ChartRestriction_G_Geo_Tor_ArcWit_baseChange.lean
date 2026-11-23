-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_ArcWit_baseChange
-- name    : ReciprocityTheory.ChartRestriction.G.Geo.Tor.ArcWit.baseChange
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T10:08:25.890906+00:00
-- url     : https://prove2.me/theorems/1691c279-163f-4ab9-a730-db865964c7b5
-- title:
--   Arc Wit: base Change
-- statement:
--   The Arc Wit construction uses the base Change property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/ToroidalCompactification/RigIsoCongr.lean#L87-L261
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/ToroidalCompactification/RigIsoCongr.lean#L87-L261

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_BCTools
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RigIsoCongr
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_comp

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi
open scoped CategoryTheory.Obj
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}
variable {D : Datum H} {l : Level H} {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}
set_option maxHeartbeats 1600000

theorem ReciprocityTheory.ChartRestriction.G.Geo.Tor.ArcWit.baseChange (hC : Out.CubePullSt) (hP : Out.PolBaseChangeSt) (hU : Out.UnifBaseChangeSt) (h5 : Out.Laws5)
    (hQ : QkPullExistsSt) (hO : PolOActPullSt) {Y : Model Xo c β} {O' : Type} [CommRing O'] [IsDomain O']
    {b : O →+* O'} {a : ArcIn D l β O' b} {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R']
    {I : Ideal R} {I' : Ideal R'} (hR : Out.AdmBase R I) (hR' : Out.AdmBase R' I') {f : O' →+* R} {u : R}
    {χ : Sp R ⟶ Y.X} (W : ArcWit Y a I f u χ) (g : R →+* R') (hg : Function.Injective g) (hI : I.map g ≤ I') :
    ∃ (W' : ArcWit Y a I' (g.comp f) (g u) (spMap g ≫ χ)) (hD : Out.IsPullDeg g W.P.D.toPre W'.P.D.toPre)
      (bc : W'.t.G ≅ (Over.pullback (Out.specOf g)).obj W.t.G), IsMonHom bc.hom ∧ Out.IsPullUnif g hD bc W.P.U W'.P.U ∧
      W'.m.φ = (bc.hom.left ≫ pullback.fst W.t.G.hom (Out.specOf g)) ≫ W.m.φ ∧
      (∀ y, hD.xe (W'.e y) = W.e y) ∧
      ∃ w' : LB.Iso W'.P.D.toPre.P.L (a.D₀.P.L.pull
          ((hD.e.hom.left ≫ pullback.fst W.P.D.toPre.P.A.hom (Out.specOf g)) ≫ W.φ)),
        W'.φ = (hD.e.hom.left ≫ pullback.fst W.P.D.toPre.P.A.hom (Out.specOf g)) ≫ W.φ ∧ HEq W'.w w' ∧
          Tri W.w hD.w w' := by sorry
