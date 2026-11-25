-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Out_powPr_zero
-- name    : ReciprocityTheory.ChartRestriction.G.Out.powPr_zero
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T14:24:47.604261+00:00
-- url     : https://prove2.me/theorems/ee87efcc-3207-5d20-a0d1-a48abb966efd
-- title:
--   Out: pow Pr zero
-- statement:
--   The Out construction uses the pow Pr zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ExtensionDescent/DegProd.lean#L86-L86
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ExtensionDescent/DegProd.lean#L86-L86

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_CubicalStructures_CubicalPullBaseChangeSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_NonzeroLocus
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_DegProd
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
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out
open Semi
variable {S : Scheme.{0}}

theorem ReciprocityTheory.ChartRestriction.G.Out.powPr_zero (G : Over S) (n : ℕ) : powPr G (n := n + 1) 0 = fst _ _ := by sorry
