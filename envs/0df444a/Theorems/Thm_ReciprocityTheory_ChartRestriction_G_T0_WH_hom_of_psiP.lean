-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_WH_hom_of_psiP
-- name    : ReciprocityTheory.ChartRestriction.G.T0.WH.hom_of_psiP
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T10:37:09.081772+00:00
-- url     : https://prove2.me/theorems/f831c863-6773-53ea-8855-4dcf2c540718
-- title:
--   WH: hom of psi P
-- statement:
--   The WH construction uses the hom of psi P property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/CoeffPsiPNeZero.lean#L80-L85
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/CoeffPsiPNeZero.lean#L80-L85

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_AevalElimEqRenameLinearSubstitution
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_CoeffPsiPNeZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.T0 ReciprocityTheory.ChartRestriction.G.T0.WH
open MvPolynomial
variable {K : Type*} [Field K] {σ : Type*} [Fintype σ] (p : σ → Prop) [DecidablePred p]

theorem ReciprocityTheory.ChartRestriction.G.T0.WH.hom_of_psiP (n : ℕ) (f : MvPolynomial σ K) (hf : psiP p f = Polynomial.C f * Polynomial.X ^ n) :
    ∀ s ∈ f.support, wt p s = n := by sorry
