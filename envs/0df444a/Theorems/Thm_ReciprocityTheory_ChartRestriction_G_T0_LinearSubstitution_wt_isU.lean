-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_LinearSubstitution_wt_isU
-- name    : ReciprocityTheory.ChartRestriction.G.T0.LinearSubstitution.wt_isU
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T15:19:56.963473+00:00
-- url     : https://prove2.me/theorems/b195eb32-1159-59a9-8574-d289f5c3c930
-- title:
--   Linear Substitution: wt is U
-- statement:
--   The Linear Substitution construction uses the wt is U property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/SubstitutionSplitIrreducibleOf.lean#L21-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/SubstitutionSplitIrreducibleOf.lean#L21-L24

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_PowFirstVarDvdSubstitution
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_EvalOneBilinearSubstitution
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_SubstitutionSplitIrreducibleOf
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.T0
open NumberField MvPolynomial
open ReciprocityTheory.ChartRestriction.G.T0.LinearSubstitution
variable {K : Type} [Field K] {D N : ℕ}

theorem ReciprocityTheory.ChartRestriction.G.T0.LinearSubstitution.wt_isU (s : V D N →₀ ℕ) : WH.wt isU s = ∑ p, s (Sum.inl p) := by sorry
