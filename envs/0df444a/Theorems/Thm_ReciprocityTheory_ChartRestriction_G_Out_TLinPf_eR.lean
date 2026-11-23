-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Out_TLinPf_eR
-- name    : ReciprocityTheory.ChartRestriction.G.Out.TLinPf.eR
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:24:46.236353+00:00
-- url     : https://prove2.me/theorems/b93e96ad-5d3d-47d6-b0ec-a6f3a5d7acd7
-- title:
--   TLin Pf: e R
-- statement:
--   The TLin Pf construction uses the e R property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ExtensionDescent/ChartPullbacks/TangentLinearity/OrbitMapConjSmulZero.lean#L119-L154
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ExtensionDescent/ChartPullbacks/TangentLinearity/OrbitMapConjSmulZero.lean#L119-L154

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
variable {U ιD e a χ}

theorem ReciprocityTheory.ChartRestriction.G.Out.TLinPf.eR (f g : D.toPre.P.A ⟶ D.toPre.P.A) (X P : (Over.map (thick R I e)).obj (thickObj R I e G) ⟶ D.toPre.P.A) :
    (lift X P).left ≫ rosatiφ D.toPre.P.A f g 0 = (padd D.toPre.P.A (X ≫ f) P).left ∧
    (lift X P).left ≫ rosatiφ D.toPre.P.A f g 1 = (X ≫ f).left ∧
    (lift X P).left ≫ rosatiφ D.toPre.P.A f g 2 = P.left ∧
    (lift X P).left ≫ rosatiφ D.toPre.P.A f g 3 = (padd D.toPre.P.A X (P ≫ g)).left ∧
    (lift X P).left ≫ rosatiφ D.toPre.P.A f g 4 = X.left ∧
    (lift X P).left ≫ rosatiφ D.toPre.P.A f g 5 = (P ≫ g).left := by sorry
