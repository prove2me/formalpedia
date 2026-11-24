-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_ArcWit_uwIso
-- name    : ReciprocityTheory.ChartRestriction.G.Geo.Tor.ArcWit.uwIso
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T08:59:46.633158+00:00
-- url     : https://prove2.me/theorems/b9d179cc-0951-4281-a9f1-d6708c1f64f8
-- title:
--   Arc Wit: uw Iso
-- statement:
--   The Arc Wit construction uses the uw Iso property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/ToroidalCompactification/SabMapCubical.lean#L46-L66
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/ToroidalCompactification/SabMapCubical.lean#L46-L66

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RigIsoCongr
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RigidSys
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SabMapCubical
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

theorem ReciprocityTheory.ChartRestriction.G.Geo.Tor.ArcWit.uwIso {Y : Model Xo c β} {O' : Type} [CommRing O'] [IsDomain O'] {b : O →+* O'} {a : ArcIn D l β O' b}
    {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {f : O' →+* R} {u : R} {χ : Sp R ⟶ Y.X}
    (W W' : ArcWit Y a I f u χ) :
    ∃ ψ : W.t.G ≅ W'.t.G, ψ.hom.left ≫ W'.m.φ = W.m.φ ∧ IsMonHom ψ.hom ∧
      (∀ x, W.t.act.act x ≫ ψ.hom = ψ.hom ≫ W'.t.act.act x) ∧
      (∀ (T : Scheme.{0}) (g : T ⟶ W.t.G.left) (g₁ : T ⟶ Y.oF.t.G.left) (g₂ : T ⟶ Y.oF.t.G.left),
        g ≫ W.m.φ = g₁ ≫ Y.m.φ → g₁ ≫ Y.m0.toSABMap.φ = g₂ ≫ Y.m0.toSABMap.φ →
        g₁ ≫ Y.oF.t.G.hom = g₂ ≫ Y.oF.t.G.hom → g ≫ ψ.hom.left ≫ W'.m.φ = g₂ ≫ Y.m.φ) ∧
      ∃ (he : eSec W.t.G ≫ ψ.hom.left = 𝟙 _ ≫ eSec W'.t.G)
        (wL : LB.Iso W.P.U.LG.L (W'.P.U.LG.L.pull ψ.hom.left)),
        wL.IsGen ∧ LB.Gen.Maps (LB.linCombIso wL (K := PUnit) (fun _ => eSec W.t.G) (fun _ => 1)) W.P.U.LG.rig
          (rigPullOf ψ.hom.left (𝟙 _) he W'.P.U.LG.L W'.P.U.LG.rig) := by sorry
