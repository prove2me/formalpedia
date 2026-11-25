-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_LinearSubstitution_iota_injective
-- name    : ReciprocityTheory.ChartRestriction.G.T0.LinearSubstitution.iota_injective
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T10:36:40.388589+00:00
-- url     : https://prove2.me/theorems/c149dbf4-5a63-5fce-a54f-33e5ef49a3d0
-- title:
--   Linear Substitution: iota injective
-- statement:
--   The Linear Substitution construction uses the iota injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/EvalOneBilinearSubstitution.lean#L54-L58
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/EvalOneBilinearSubstitution.lean#L54-L58

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_AevalElimEqRenameLinearSubstitution
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_CoeffPsiPNeZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_EvalOneBilinearSubstitution
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.T0 ReciprocityTheory.ChartRestriction.G.T0.LinearSubstitution
open MvPolynomial
variable {K : Type} [Field K] {D N : ℕ}

theorem ReciprocityTheory.ChartRestriction.G.T0.LinearSubstitution.iota_injective : Function.Injective (iota (D := D) (N := N)) := by sorry
