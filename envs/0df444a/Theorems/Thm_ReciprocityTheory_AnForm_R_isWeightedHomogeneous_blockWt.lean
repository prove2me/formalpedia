-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_R_isWeightedHomogeneous_blockWt
-- name    : ReciprocityTheory.AnForm.R.isWeightedHomogeneous_blockWt
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T13:46:57.216196+00:00
-- url     : https://prove2.me/theorems/7d29a4f7-d161-5fee-afae-5c965fdda4a7
-- title:
--   R: is Weighted Homogeneous block Wt
-- statement:
--   The R construction uses the is Weighted Homogeneous block Wt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/RegularLocalRings/ConeChartA.lean#L223-L233
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/RegularLocalRings/ConeChartA.lean#L223-L233

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

theorem ReciprocityTheory.AnForm.R.isWeightedHomogeneous_blockWt {f : MvPolynomial (Σ k, ι k) ℂ} {dg : K → ℕ}
    (hf : IsMultiHomog f dg) (k : K) : IsWeightedHomogeneous (blockWt k) f (dg k) := by sorry
