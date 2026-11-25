-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Out_unifBaseChangeInj_of_seamsCS
-- name    : ReciprocityTheory.ChartRestriction.G.Out.unifBaseChangeInj_of_seamsCS
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T14:15:10.222691+00:00
-- url     : https://prove2.me/theorems/a24e597c-21c7-4719-85b0-b26cb4693a13
-- title:
--   Out: unif Base Change Inj of seams CS
-- statement:
--   The Out construction uses the unif Base Change Inj of seams CS property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ExtensionDescent/ChartPullbacks/UniformBaseChange/UnifBaseChangeInjOfSeamsCS.lean#L253-L263
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ExtensionDescent/ChartPullbacks/UniformBaseChange/UnifBaseChangeInjOfSeamsCS.lean#L253-L263

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifBaseChangeSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_UniformBaseChange_UnifBaseChangeInjOfSeamsCS
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
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out
open Semi

theorem ReciprocityTheory.ChartRestriction.G.Out.unifBaseChangeInj_of_seamsCS (h1 : PullDegCSInjSt) (h2 : PullPreCSInjSt)
    (h3 : ExpPullInjSt) : UnifBaseChangeInjSt := by sorry
