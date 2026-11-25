-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Out_powPr_succ
-- name    : ReciprocityTheory.ChartRestriction.G.Out.powPr_succ
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T14:29:18.820461+00:00
-- url     : https://prove2.me/theorems/10529c36-5f95-48a8-aa6c-200b91553b82
-- title:
--   Out: pow Pr succ
-- statement:
--   The Out construction uses the pow Pr succ property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ExtensionDescent/DegProd.lean#L88-L89
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ExtensionDescent/DegProd.lean#L88-L89

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

theorem ReciprocityTheory.ChartRestriction.G.Out.powPr_succ (G : Over S) (n : ℕ) (i : Fin n) :
    powPr G (n := n + 1) i.succ = snd _ _ ≫ powPr G i := by sorry
