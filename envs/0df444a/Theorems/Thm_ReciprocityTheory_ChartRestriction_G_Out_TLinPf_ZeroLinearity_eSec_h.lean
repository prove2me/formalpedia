-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Out_TLinPf_ZeroLinearity_eSec_h
-- name    : ReciprocityTheory.ChartRestriction.G.Out.TLinPf.ZeroLinearity.eSec_h
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T10:31:50.265+00:00
-- url     : https://prove2.me/theorems/29a8a730-12a1-4f02-9ee8-c29514b21180
-- title:
--   Zero Linearity: e Sec h
-- statement:
--   The Zero Linearity construction uses the e Sec h property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ExtensionDescent/ChartPullbacks/TangentLinearity/ResEqOfResEq.lean#L207-L211
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ExtensionDescent/ChartPullbacks/TangentLinearity/ResEqOfResEq.lean#L207-L211

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
open ReciprocityTheory.ChartRestriction.G.Out.TLinPf.ZeroLinearity
variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {O : Type} [Ring O] [StarRing O]
  {D : DegData R I} {A : PolAV (Spec (CommRingCat.of (FractionRing R)))}
  {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G] (U : UnifPre I D A G)
  (ιG : RingAct G O) (e : ℕ) (a : O)

theorem ReciprocityTheory.ChartRestriction.G.Out.TLinPf.ZeroLinearity.eSec_h : eSec (thickObj R I e G) ≫ ((Over.pullback (thick R I e)).map (ιG.act a)).left =
    eSec (thickObj R I e G) := by sorry
