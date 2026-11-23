-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Out_TLinPf_hA
-- name    : ReciprocityTheory.ChartRestriction.G.Out.TLinPf.hA
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T13:24:42.536797+00:00
-- url     : https://prove2.me/theorems/636c0699-7a21-497e-b399-0593a1e4b674
-- title:
--   TLin Pf: h A
-- statement:
--   The TLin Pf construction uses the h A property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ExtensionDescent/ChartPullbacks/TangentLinearity/OrbitMapConjSmulZero.lean#L225-L248
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ExtensionDescent/ChartPullbacks/TangentLinearity/OrbitMapConjSmulZero.lean#L225-L248

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_TangentLinearity_FnOfComp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_CanonGenIsGen
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifBaseChangeSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_TangentLinearity_OrbitMapConjSmulZero
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

theorem ReciprocityTheory.ChartRestriction.G.Out.TLinPf.hA : φA U ιD e a χ = Sum.elim
    ![(padd D.toPre.P.A (U.gt e).pG (xc e χ (G := G) ≫ ιD.onB.act (star a))).left,
      (xc e χ (G := G) ≫ ιD.onB.act (star a)).left, (U.gt e).pG.left,
      (toUnit ((Over.map (thick R I e)).obj (thickObj R I e G)) ≫ η[D.toPre.P.A]).left]
    ![(padd D.toPre.P.A (xc e χ (G := G) ≫ ιD.onB.act (star a)) (U.gt e).pG).left,
      (xc e χ (G := G) ≫ ιD.onB.act (star a)).left, (U.gt e).pG.left,
      (padd D.toPre.P.A (xc e χ (G := G)) ((U.gt e).pG ≫ ιD.onB.act a)).left,
      (xc e χ (G := G)).left, ((U.gt e).pG ≫ ιD.onB.act a).left] := by sorry
