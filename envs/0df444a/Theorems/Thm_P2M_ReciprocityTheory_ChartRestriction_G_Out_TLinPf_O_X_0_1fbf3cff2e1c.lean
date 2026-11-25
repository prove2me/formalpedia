-- Prove2me | Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_Out_TLinPf_O_X_0_1fbf3cff2e1c
-- name    : P2M_ReciprocityTheory_ChartRestriction_G_Out_TLinPf_O_X_0_1fbf3cff2e1c
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T13:48:49.534057+00:00
-- url     : https://prove2.me/theorems/e40cc74d-7191-5c89-8e46-86bfef37c052
-- title:
--   P2 M Reciprocity Theory Chart Restriction G Out TLin Pf O X 0 1fbf3cff2e1c: P2 M Reciprocity Theory Chart Restriction G Out TLin Pf O X 0 1fbf3cff2e1c
-- statement:
--   The P2 M Reciprocity Theory Chart Restriction G Out TLin Pf O X 0 1fbf3cff2e1c construction uses the P2 M Reciprocity Theory Chart Restriction G Out TLin Pf O X 0 1fbf3cff2e1c property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ExtensionDescent/ChartPullbacks/TangentLinearity/OrbitMapConjSmulZero.lean#L93-L94
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ExtensionDescent/ChartPullbacks/TangentLinearity/OrbitMapConjSmulZero.lean#L93-L94

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
omit [Module O D.toPre.X]

theorem P2M_ReciprocityTheory_ChartRestriction_G_Out_TLinPf_O_X_0_1fbf3cff2e1c {T : Over (Spec (CommRingCat.of R))} (P x : T ⟶ D.toPre.P.A) :
    OφX (D := D) P x 0 = (padd D.toPre.P.A P x).left := by sorry

alias «ReciprocityTheory».«ChartRestriction».«G».«Out».«TLinPf».«OφX_0» := P2M_ReciprocityTheory_ChartRestriction_G_Out_TLinPf_O_X_0_1fbf3cff2e1c
