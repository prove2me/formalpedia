-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_LinearSubstitution_evalOne_bilinearSubstitution
-- name    : ReciprocityTheory.ChartRestriction.G.T0.LinearSubstitution.evalOne_bilinearSubstitution
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T10:37:18.197014+00:00
-- url     : https://prove2.me/theorems/3ddb56d8-9eaa-4d13-aec9-2bd3e89d77c5
-- title:
--   Linear Substitution: eval One bilinear Substitution
-- statement:
--   The Linear Substitution construction uses the eval One bilinear Substitution property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/EvalOneBilinearSubstitution.lean#L68-L84
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/EvalOneBilinearSubstitution.lean#L68-L84

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

theorem ReciprocityTheory.ChartRestriction.G.T0.LinearSubstitution.evalOne_bilinearSubstitution (F : KTp K D N) : ev1 (bilinearSubstitution F) = theta (rename iota F) := by sorry
