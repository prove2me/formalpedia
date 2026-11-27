-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Out_OLinPf_ILin_val_maps
-- name    : ReciprocityTheory.ChartRestriction.G.Out.OLinPf.ILin.val_maps
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T14:28:42.308267+00:00
-- url     : https://prove2.me/theorems/00db08d0-d44c-52b5-84e0-793348eec6ed
-- title:
--   ILin: val maps
-- statement:
--   The ILin construction uses the val maps property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ExtensionDescent/ChartPullbacks/LinearRestriction/ResPullUVal.lean#L52-L90
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ExtensionDescent/ChartPullbacks/LinearRestriction/ResPullUVal.lean#L52-L90

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_OLinBaseChangeSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_UniformBaseChange_PullGt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_WeightedChartPullback_CancelSecAct
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_LinearRestriction_ResPullUVal
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
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj
  AlgebraicGeometry
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Out.OLinPf
open ReciprocityTheory.ChartRestriction.G.Out Semi
variable {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R']
variable {I : Ideal R} {I' : Ideal R'} (φ : R →+* R') {D : DegData R I}
  {A : PolAV (Spec (CommRingCat.of (FractionRing R)))}
  {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G] {U : Unif I D A G}
  {G' : Over (Spec (CommRingCat.of R'))} [GrpObj G'] [IsCommMonObj G']
  {bc : G' ≅ (Over.pullback (specOf φ)).obj G}
  {A' : PolAV (Spec (CommRingCat.of (FractionRing R')))} {D' : DegData R' I'}
  {hD : IsPullDeg φ D.toPre D'.toPre} {U' : Unif I' D' A' G'}
  {O : Type} [CommRing O] [StarRing O]
open ReciprocityTheory.ChartRestriction.G.Out.OLinPf.ILin
open Geo.Tor

theorem ReciprocityTheory.ChartRestriction.G.Out.OLinPf.ILin.val_maps {X X' Y Y' Z : Scheme.{0}} {L : LB X} {L' : LB X'} (F : X' ⟶ X)
    (w : LB.Iso L' (L.pull F)) {K : Type} [Fintype K] (φ : K → (Y ⟶ X)) (ε : K → ℤ)
    (ψ : K → (Y' ⟶ X')) (h : Y' ⟶ Y) (hψ : ∀ k, ψ k ≫ F = h ≫ φ k)
    (t : LB.Gen (LB.LinComb L φ ε)) (t' : LB.Gen (LB.LinComb L' ψ ε))
    (hm : LB.Gen.Maps (LB.linCombIso w ψ ε) t' (GeneratorPullback.pullAlong L F h φ ε ψ hψ t))
    (r : Z ⟶ Y') (z : Z) (J' : (Z ⟶ X') → L'.ι) (J : (Z ⟶ X) → L.ι)
    (hJ' : Good L' z J') (hJ : Good L z J) :
    val t (r ≫ h) z J =
      (∏ k, gm (r ≫ ψ k) z _ (w.s (fun _ => J ((r ≫ ψ k) ≫ F), J' (r ≫ ψ k))) ^ ε k) *
        val t' r z J' := by sorry
