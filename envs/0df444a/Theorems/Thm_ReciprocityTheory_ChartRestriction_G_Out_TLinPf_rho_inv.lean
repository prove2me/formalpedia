-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Out_TLinPf_rho_inv
-- name    : ReciprocityTheory.ChartRestriction.G.Out.TLinPf.rho_inv
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T10:32:45.058645+00:00
-- url     : https://prove2.me/theorems/e234a955-6d8b-5f59-b6c3-184a1a20cdb5
-- title:
--   TLin Pf: rho inv
-- statement:
--   The TLin Pf construction uses the rho inv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ExtensionDescent/ChartPullbacks/TangentLinearity/CompBaseEq.lean#L129-L155
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ExtensionDescent/ChartPullbacks/TangentLinearity/CompBaseEq.lean#L129-L155

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_TangentLinearity_PairProp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_TangentLinearity_WchartInlLe
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_TangentLinearity_ActActA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_TangentLinearity_CompBaseEq
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
  CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Out.TLinPf
open Semi
variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {O : Type} [Ring O] [StarRing O]
  {D : DegData R I} [Module O D.toPre.X] {A : PolAV (Spec (CommRingCat.of (FractionRing R)))}
  {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G] (U : UnifPre I D A G)
  (ιD : D.OAct O) (ιG : RingAct G O) (e : ℕ) (a : O) (χ : D.toPre.X)
  (hO : ∀ a : O, (Over.pullback (thick R I e)).map (ιG.act a) ≫ (U.gt e).q =
      (U.gt e).q ≫ (Over.pullback (thick R I e)).map (ιD.onB.act a))
  (u : LB.Gen (LB.LinComb D.toPre.P.L
    (rosatiφ D.toPre.P.A (ιD.onB.act (star a)) (ιD.onB.act a)) rosatiε))
include hO

theorem ReciprocityTheory.ChartRestriction.G.Out.TLinPf.rho_inv
    (hi : ∃ t : splitTorus (Spec (CommRingCat.of (R ⧸ I ^ (e + 1)))) D.toPre.X ⟶
        splitTorus (Spec (CommRingCat.of (R ⧸ I ^ (e + 1)))) D.toPre.X,
      TorusEndOf D.toPre.X (fun χ => star a • χ) t ∧
        (U.gt e).i ≫ (Over.pullback (thick R I e)).map (ιG.act a) = t ≫ (U.gt e).i)
    (ρ : Γ((thickObj R I e G).left, ⊤)ˣ) (hρ : PairProp U ιD ιG e a χ u ρ) :
    (WeightPf.act (U.gt e)).left.appTop.hom ρ.val =
      (snd (WeightPf.Te D.toPre I e) (thickObj R I e G)).left.appTop.hom ρ.val := by sorry
