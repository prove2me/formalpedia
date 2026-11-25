-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_H1_weil_move
-- name    : ReciprocityTheory.ChartRestriction.G.H1.weil_move
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T10:31:06.044991+00:00
-- url     : https://prove2.me/theorems/6885ce88-0623-4907-8390-2c049beea621
-- title:
--   H1: weil move
-- statement:
--   The H1 construction uses the weil move property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FirstCohomology/TateTransport.lean#L30-L62
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FirstCohomology/TateTransport.lean#L30-L62

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_OneCHyp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_ThetaMove
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_BCTools
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_TateTransport
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
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
  CartesianMonoidalCategory MonObj IsLocalRing NumberField
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.H1
open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

theorem ReciprocityTheory.ChartRestriction.G.H1.weil_move (hW : WeilSt) {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {R : Type} [CommRing R]
    [IsDomain R] {I : Ideal R} {t : SAB H (Sp R)} (P : PELUnif I t) (F : Type) [Field F] [Algebra (FractionRing R) F]
    {φ : P.A.A.left ⟶ t.G.left} (hp : IsGrpPullback P.A.A t.G (jK R) φ)
    (w : LB.Iso P.A.L (t.PP.L.pull φ)) (hw : w.IsGen)
    (n : ℕ) (x y : TFK (R := R) F ⟶ P.A.A) (hx : x ^ n = 1) (hy : y ^ n = 1) (c : Γ(Sp F, ⊤)ˣ)
    (hG : WeilIs t.G t.PP.L n (pushPt hp.1.w x) (pushPt hp.1.w y) c) : WeilIs P.A.A P.A.L n x y c := by sorry
