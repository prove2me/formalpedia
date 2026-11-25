-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_ArcWit_uwMove
-- name    : ReciprocityTheory.ChartRestriction.G.Geo.Tor.ArcWit.uwMove
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T10:25:16.572051+00:00
-- url     : https://prove2.me/theorems/4c400627-84e2-419f-862f-8ac723b04633
-- title:
--   Arc Wit: uw Move
-- statement:
--   The Arc Wit construction uses the uw Move property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/ToroidalCompactification/AdmissibleBasePowerSeries.lean#L27-L115
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/ToroidalCompactification/AdmissibleBasePowerSeries.lean#L27-L115

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SabMapCubical
import Definitions.Def_ReciprocityTheory_AdicCompleteness_IsAdicCompleteComapConstantCoeff
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_AdmissibleBasePowerSeries
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

theorem ReciprocityTheory.ChartRestriction.G.Geo.Tor.ArcWit.uwMove (hU : Out.UnifBaseChangeSt) (h5 : Out.Laws5) {Y : Model Xo c β} {O' : Type} [CommRing O']
    [IsDomain O'] {b : O →+* O'} {a : ArcIn D l β O' b} {R : Type} [CommRing R] [IsDomain R] {I : Ideal R}
    (hR : Out.AdmBase R I) {f : O' →+* R} {u : R} {χ : Sp R ⟶ Y.X} (W W' : ArcWit Y a I f u χ) (ψ : W.t.G ≅ W'.t.G)
    [IsMonHom ψ.hom] (hφ : ψ.hom.left ≫ W'.m.φ = W.m.φ) (hact : ∀ x, W.t.act.act x ≫ ψ.hom = ψ.hom ≫ W'.t.act.act x) :
    ∃ (bc : W.t.G ≅ (Over.pullback (Out.specOf (RingHom.id R))).obj W'.t.G) (D'' : Out.DegData R I)
      (hD : Out.IsPullDeg (RingHom.id R) W'.P.D.toPre D''.toPre) (U'' : Out.Unif I D'' W'.P.A W.t.G)
      (_ : Module (𝓞 E) D''.toPre.X) (oD : letI := H.starRing; D''.toPre.OAct (𝓞 E)),
      IsMonHom bc.hom ∧ bc.hom.left ≫ pullback.fst W'.t.G.hom (Out.specOf (RingHom.id R)) = ψ.hom.left ∧
      U''.LG = W.P.U.LG ∧
      U''.gen.hom.left ≫ W'.P.U.gen.inv.left ≫ pullback.fst W'.t.G.hom (Out.jK R) =
        pullback.fst W.t.G.hom (Out.jK R) ≫ ψ.hom.left ∧
      Out.IsPullUnif (RingHom.id R) hD bc W'.P.U U'' ∧
      (∀ (x : 𝓞 E) y, hD.xe (x • y) = x • hD.xe y) ∧
      (letI := H.starRing; ∀ x, oD.onB.act x ≫ hD.e.hom =
        hD.e.hom ≫ (Over.pullback (Out.specOf (RingHom.id R))).map (W'.P.oD.onB.act x)) ∧
      (letI := H.starRing; U''.toUnifPre.OLinear (𝓞 E) oD W'.P.oA W.t.act.toRingAct) ∧
      (letI := H.starRing; TraceFormTwistIso D''.toPre oD H.w0) := by sorry
