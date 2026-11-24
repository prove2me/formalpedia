-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_ArcWit_witMove
-- name    : ReciprocityTheory.ChartRestriction.G.Geo.Tor.ArcWit.witMove
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T09:01:27.973864+00:00
-- url     : https://prove2.me/theorems/07ff7417-13eb-4f58-8471-31e0d5dc7390
-- title:
--   Arc Wit: wit Move
-- statement:
--   The Arc Wit construction uses the wit Move property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/ToroidalCompactification/WitMove.lean#L16-L153
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/ToroidalCompactification/WitMove.lean#L16-L153

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CocycleIdentityIso
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_WitMove
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

theorem ReciprocityTheory.ChartRestriction.G.Geo.Tor.ArcWit.witMove (h5 : Out.Laws5) (hQ : QkPullExistsSt) {Y : Model Xo c β} {O' : Type} [CommRing O']
    [IsDomain O'] {b : O →+* O'} {a : ArcIn D l β O' b} {R : Type} [CommRing R] [IsDomain R] {I : Ideal R}
    (hR : Out.AdmBase R I) {f : O' →+* R} {u : R} {χ : Sp R ⟶ Y.X} (W : ArcWit Y a I f u χ) {G'' : Over (Sp R)}
    [GrpObj G''] [IsCommMonObj G''] {D'' : Out.DegData R I} [Module (𝓞 E) D''.toPre.X]
    {A'' : Out.PolAV (Sp (FractionRing R))} (U'' : Out.Unif I D'' A'' G'')
    (oD'' : letI := H.starRing; D''.toPre.OAct (𝓞 E))
    (bc : G'' ≅ (Over.pullback (Out.specOf (RingHom.id R))).obj W.t.G) [IsMonHom bc.hom]
    (hD : Out.IsPullDeg (RingHom.id R) W.P.D.toPre D''.toPre) (hPU : Out.IsPullUnif (RingHom.id R) hD bc W.P.U U'')
    (xl : ∀ (x : 𝓞 E) y, hD.xe (x • y) = x • hD.xe y)
    (el : letI := H.starRing; ∀ x, oD''.onB.act x ≫ hD.e.hom =
      hD.e.hom ≫ (Over.pullback (Out.specOf (RingHom.id R))).map (W.P.oD.onB.act x)) :
    letI := H.starRing
    ∃ (he'' : eSec D''.toPre.P.A ≫ (hD.e.hom.left ≫ pullback.fst W.P.D.toPre.P.A.hom (Out.specOf (RingHom.id R))) ≫
        W.φ = spMap f ≫ eSec a.D₀.P.A)
      (w'' : LB.Iso D''.toPre.P.L (a.D₀.P.L.pull
        ((hD.e.hom.left ≫ pullback.fst W.P.D.toPre.P.A.hom (Out.specOf (RingHom.id R))) ≫ W.φ)))
      (e'' : a.D₀.X ≃ₗ[𝓞 E] D''.toPre.X),
      (∀ y, hD.xe (e'' y) = W.e y) ∧ Tri W.w hD.w w'' ∧
      IsGrpPullback D''.toPre.P.A a.D₀.P.A (spMap f)
        ((hD.e.hom.left ≫ pullback.fst W.P.D.toPre.P.A.hom (Out.specOf (RingHom.id R))) ≫ W.φ) ∧ w''.IsGen ∧
      LB.Gen.Maps (LB.linCombIso w'' (K := PUnit) (fun _ => eSec D''.toPre.P.A) (fun _ => 1)) D''.toPre.rig
        (rigPullOf ((hD.e.hom.left ≫ pullback.fst W.P.D.toPre.P.A.hom (Out.specOf (RingHom.id R))) ≫ W.φ)
          (spMap f) he'' a.D₀.P.L a.D₀.rig) ∧
      (∀ x, (oD''.onB.act x).left ≫
          (hD.e.hom.left ≫ pullback.fst W.P.D.toPre.P.A.hom (Out.specOf (RingHom.id R))) ≫ W.φ =
        ((hD.e.hom.left ≫ pullback.fst W.P.D.toPre.P.A.hom (Out.specOf (RingHom.id R))) ≫ W.φ) ≫
          (a.oa.onB.act x).left) ∧
      (∀ y, (D''.toPre.c (e'' y)).left ≫
          (hD.e.hom.left ≫ pullback.fst W.P.D.toPre.P.A.hom (Out.specOf (RingHom.id R))) ≫ W.φ =
        spMap f ≫ (a.D₀.c y).left) ∧
      ∀ (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] [Algebra (FractionRing O') F] (uF : F),
        (∀ x, algebraMap (FractionRing O') F (algebraMap O' _ x) =
          algebraMap (FractionRing R) F (algebraMap R _ (f x))) →
        uF = algebraMap (FractionRing R) F (algebraMap R _ u) →
        (∀ y, GenRel w'' (LB.pullGen _ _ _ (D''.toPre.psi (e'' y)) (Out.jFK (R := R) F))
          (LB.pullGen _ _ _ (a.D₀.psi y) (Out.jFK (R := O') F)) (uF ^ (a.be y y / 2))) ∧
        ∀ (yF : Sp F ⟶ Xo.XF c), yF ≫ Y.j = Out.jFK (R := R) F ≫ Out.jK R ≫ χ →
          ∀ (k : ℕ) (p₀ : Out.QkPt a.D₀ (FractionRing O') k) (σ : 𝟙_ (Over (Xo.XF c)) ⟶ Y.oF.t.G),
            ((k = l.A ∧ ∃ v, HEq p₀ (a.etaA v) ∧ σ = Y.oF.etaA v) ∨
              (k = l.M ∧ ∃ v ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) D.La),
                HEq p₀ (a.eta v) ∧ σ = Y.oF.eta v)) →
            ∀ (q₀ : Out.QkPt a.D₀ F k) (q : Out.QkPt D''.toPre F k) (x : Out.TFK (R := R) F ⟶ A''.A),
              QkExt (algebraMap _ F) p₀ q₀ → q.y = e'' q₀.y →
              (∀ z, GenRel w'' (q.g.s (e'' z)) (q₀.g.s z) (uF ^ (a.be q₀.y z / k))) →
              x.left ≫ U''.gen.inv.left ≫ pullback.fst G''.hom (Out.jK R) ≫ bc.hom.left ≫
                pullback.fst W.t.G.hom (Out.specOf (RingHom.id R)) ≫ W.m.φ = yF ≫ σ.left ≫ Y.m.φ →
              Out.QkToAkU U''.toUnifPre F k q x := by sorry
