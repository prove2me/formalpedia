-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_LinearSubstitution_eq_monomial_of_dehomog_const
-- name    : ReciprocityTheory.ChartRestriction.G.T0.LinearSubstitution.eq_monomial_of_dehomog_const
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T15:21:40.568975+00:00
-- url     : https://prove2.me/theorems/d5c731d4-d608-4a33-a7a4-238f48dd1a99
-- title:
--   Linear Substitution: eq monomial of dehomog const
-- statement:
--   The Linear Substitution construction uses the eq monomial of dehomog const property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/SubstitutionSplitIrreducibleOf.lean#L64-L138
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/SubstitutionSplitIrreducibleOf.lean#L64-L138

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

theorem ReciprocityTheory.ChartRestriction.G.T0.LinearSubstitution.eq_monomial_of_dehomog_const (A : MvPolynomial (V D N) K) (m : ℕ) (hA : ∀ s ∈ A.support, WH.wt isX s = m)
    (k : K) (h1 : ev1 A = C k) : A = C k * X (Sum.inr 0) ^ m := by sorry
