-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_WH_coeff_psiP_ne_zero
-- name    : ReciprocityTheory.ChartRestriction.G.T0.WH.coeff_psiP_ne_zero
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:03:04.009823+00:00
-- url     : https://prove2.me/theorems/270ddbc0-3b61-4d95-962e-674b7cf5be43
-- title:
--   WH: coeff psi P ne zero
-- statement:
--   The WH construction uses the coeff psi P ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/CoeffPsiPNeZero.lean#L66-L78
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/CoeffPsiPNeZero.lean#L66-L78

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

theorem ReciprocityTheory.ChartRestriction.G.T0.WH.coeff_psiP_ne_zero (f : MvPolynomial σ K) (s : σ →₀ ℕ) (hs : s ∈ f.support) :
    (psiP p f).coeff (wt p s) ≠ 0 := by sorry
