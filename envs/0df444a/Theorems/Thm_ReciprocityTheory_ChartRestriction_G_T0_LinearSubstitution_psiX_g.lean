-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_LinearSubstitution_psiX_g
-- name    : ReciprocityTheory.ChartRestriction.G.T0.LinearSubstitution.psiX_g
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T15:33:25.799335+00:00
-- url     : https://prove2.me/theorems/c32a5261-1693-4623-b584-37db9aa1bfd1
-- title:
--   Linear Substitution: psi X g
-- statement:
--   The Linear Substitution construction uses the psi X g property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/SubstitutionSplitIrreducibleOf.lean#L54-L57
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/SubstitutionSplitIrreducibleOf.lean#L54-L57

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

theorem ReciprocityTheory.ChartRestriction.G.T0.LinearSubstitution.psiX_g (t : TVar D N) :
    WH.psiP isX (gImg (K := K) t) = Polynomial.C (gImg t) * Polynomial.X := by sorry
