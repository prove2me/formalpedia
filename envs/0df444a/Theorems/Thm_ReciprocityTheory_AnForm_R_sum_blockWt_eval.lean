-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_R_sum_blockWt_eval
-- name    : ReciprocityTheory.AnForm.R.sum_blockWt_eval
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T13:47:03.38147+00:00
-- url     : https://prove2.me/theorems/57521495-5b9b-5685-b1ec-c59dd3fddd49
-- title:
--   R: sum block Wt eval
-- statement:
--   The R construction uses the sum block Wt eval property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/RegularLocalRings/ConeChartA.lean#L235-L239
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/RegularLocalRings/ConeChartA.lean#L235-L239

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

theorem ReciprocityTheory.AnForm.R.sum_blockWt_eval {f : MvPolynomial (Σ k, ι k) ℂ} {dg : K → ℕ} (hf : IsMultiHomog f dg)
    (k : K) (z : (Σ k, ι k) → ℂ) :
    ∑ q, (blockWt k q : ℂ) * (z q * eval z (pderiv q f)) = (dg k : ℂ) * eval z f := by sorry
