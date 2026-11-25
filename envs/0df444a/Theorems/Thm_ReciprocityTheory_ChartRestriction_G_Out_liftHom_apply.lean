-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Out_liftHom_apply
-- name    : ReciprocityTheory.ChartRestriction.G.Out.liftHom_apply
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T14:24:47.055697+00:00
-- url     : https://prove2.me/theorems/4961ad30-a543-51c1-9f17-43b952a55c95
-- title:
--   Out: lift Hom apply
-- statement:
--   The Out construction uses the lift Hom apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ExtensionDescent/ThetaVV.lean#L21-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ExtensionDescent/ThetaVV.lean#L21-L22

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ThetaPt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ThetaVV
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
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out
open Semi
variable {S : Scheme.{0}} (A : Over S) [GrpObj A]

theorem ReciprocityTheory.ChartRestriction.G.Out.liftHom_apply {T : Over S} (W : (T ⊗ A).left.Opens) (r : Γ(T.left, ⊤)) :
    liftHom A W r = liftFun A W r := by sorry
