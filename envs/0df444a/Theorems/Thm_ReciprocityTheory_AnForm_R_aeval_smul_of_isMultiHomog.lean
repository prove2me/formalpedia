-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_R_aeval_smul_of_isMultiHomog
-- name    : ReciprocityTheory.AnForm.R.aeval_smul_of_isMultiHomog
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T14:00:53.534612+00:00
-- url     : https://prove2.me/theorems/58050959-a3d0-4c30-963a-1dd17f77bded
-- title:
--   R: aeval smul of is Multi Homog
-- statement:
--   The R construction uses the aeval smul of is Multi Homog property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/RegularLocalRings/ConeChartA.lean#L81-L99
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/RegularLocalRings/ConeChartA.lean#L81-L99

import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_ProjHyp
import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_PolynomialHeights_HeightAddRingKrullDimQuotientMvPolynomialField
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_ConeChartA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.R
open MvPolynomial Algebra
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem ReciprocityTheory.AnForm.R.aeval_smul_of_isMultiHomog {T : Type*} [CommRing T] [Algebra ℂ T]
    {f : MvPolynomial (Σ k, ι k) ℂ} {a : K → ℕ}
    (hf : IsMultiHomog f a) (c : K → T) (y : (Σ k, ι k) → T) :
    aeval (fun q => c q.1 * y q) f = (∏ k, c k ^ a k) * aeval y f := by sorry
