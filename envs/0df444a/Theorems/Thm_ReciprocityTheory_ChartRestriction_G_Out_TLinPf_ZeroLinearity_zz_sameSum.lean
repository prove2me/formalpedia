-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Out_TLinPf_ZeroLinearity_zz_sameSum
-- name    : ReciprocityTheory.ChartRestriction.G.Out.TLinPf.ZeroLinearity.zz_sameSum
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T10:40:52.585363+00:00
-- url     : https://prove2.me/theorems/188e91fc-b6a1-4197-9db5-1d366fa232b7
-- title:
--   Zero Linearity: zz same Sum
-- statement:
--   The Zero Linearity construction uses the zz same Sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ExtensionDescent/ChartPullbacks/TangentLinearity/ResEqOfResEq.lean#L168-L196
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ExtensionDescent/ChartPullbacks/TangentLinearity/ResEqOfResEq.lean#L168-L196

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
variable {S : Scheme.{0}} (B : Over S) [GrpObj B] [IsCommMonObj B] (f g : B ⟶ B) [IsMonHom g]

theorem ReciprocityTheory.ChartRestriction.G.Out.TLinPf.ZeroLinearity.zz_sameSum : LB.SameSum (Y := B.left) (K := PEmpty) PEmpty.elim PEmpty.elim
    (fun k => (zz B).left ≫ rosatiφ B f g k) rosatiε := by sorry
