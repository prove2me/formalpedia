-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Out_TLinPf_u_zero
-- name    : ReciprocityTheory.ChartRestriction.G.Out.TLinPf.u_zero
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T10:33:11.760188+00:00
-- url     : https://prove2.me/theorems/a06bdbdd-ce91-55fa-b8f8-34b9b8d96203
-- title:
--   TLin Pf: u zero
-- statement:
--   The TLin Pf construction uses the u zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ExtensionDescent/ChartPullbacks/TangentLinearity/ResEqOfResEq.lean#L267-L352
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ExtensionDescent/ChartPullbacks/TangentLinearity/ResEqOfResEq.lean#L267-L352

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_TangentLinearity_PairProp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_TangentLinearity_ResEqOfResEq
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
open ZeroLinearity
variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {O : Type} [Ring O] [StarRing O]
  {D : DegData R I} [Module O D.toPre.X] {A : PolAV (Spec (CommRingCat.of (FractionRing R)))}
  {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G] (U : UnifPre I D A G)
  (ιD : D.OAct O) (ιG : RingAct G O) (e : ℕ) (a : O) (χ : D.toPre.X)
  (hO : ∀ a : O, (Over.pullback (thick R I e)).map (ιG.act a) ≫ (U.gt e).q =
      (U.gt e).q ≫ (Over.pullback (thick R I e)).map (ιD.onB.act a))
  (u : LB.Gen (LB.LinComb D.toPre.P.L
    (rosatiφ D.toPre.P.A (ιD.onB.act (star a)) (ιD.onB.act a)) rosatiε))

theorem ReciprocityTheory.ChartRestriction.G.Out.TLinPf.u_zero (hGF : GlobalFnsSt) (hu : u.IsGen)
    (hu0 : LB.Gen.Corr D.toPre.P.L _ _ _ _ (LB.pullGen D.toPre.P.L _ _ u (zero2 D.toPre.P.A))
      (LB.oneGen D.toPre.P.L)) :
    LB.Gen.Corr D.toPre.P.L _ _ _ _
      (LB.pullGen D.toPre.P.L _ _ u (lift (𝟙 D.toPre.P.A) (toUnit D.toPre.P.A ≫ η[D.toPre.P.A])).left)
      (LB.oneGen D.toPre.P.L) := by sorry
