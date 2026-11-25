-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_MHF_coeff_psiB_ne_zero
-- name    : ReciprocityTheory.ChartRestriction.G.T0.MHF.coeff_psiB_ne_zero
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T10:37:54.797467+00:00
-- url     : https://prove2.me/theorems/ece38796-41df-4a6e-8fae-8b08a44dc7ef
-- title:
--   MHF: coeff psi B ne zero
-- statement:
--   The MHF construction uses the coeff psi B ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/CoeffPsiBNeZero.lean#L45-L57
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/CoeffPsiBNeZero.lean#L45-L57

import Definitions.Def_ReciprocityTheory_SemistableReduction_SphereLogIntegrableStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_CoeffPsiBNeZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.T0 ReciprocityTheory.ChartRestriction.G.T0.MHF
open MvPolynomial ReciprocityTheory.MultiplicativeHeights
variable {K : Type*} [Field K] {B n : ℕ}

theorem ReciprocityTheory.ChartRestriction.G.T0.MHF.coeff_psiB_ne_zero (b : Fin B) (f : MvPolynomial (Fin B × Fin n) K)
    (s : Fin B × Fin n →₀ ℕ) (hs : s ∈ f.support) : (psiB b f).coeff (bw b s) ≠ 0 := by sorry
