-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_LinearSubstitution_psiU_g
-- name    : ReciprocityTheory.ChartRestriction.G.T0.LinearSubstitution.psiU_g
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T15:20:51.324945+00:00
-- url     : https://prove2.me/theorems/eb3361e3-a761-4606-b574-fcc2387f2df5
-- title:
--   Linear Substitution: psi U g
-- statement:
--   The Linear Substitution construction uses the psi U g property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/SubstitutionSplitIrreducibleOf.lean#L59-L62
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/SubstitutionSplitIrreducibleOf.lean#L59-L62

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

theorem ReciprocityTheory.ChartRestriction.G.T0.LinearSubstitution.psiU_g (t : TVar D N) :
    WH.psiP isU (gImg (K := K) t) = Polynomial.C (gImg t) * Polynomial.X := by sorry
