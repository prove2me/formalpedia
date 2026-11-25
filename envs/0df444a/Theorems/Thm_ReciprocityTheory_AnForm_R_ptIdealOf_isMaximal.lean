-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_R_ptIdealOf_isMaximal
-- name    : ReciprocityTheory.AnForm.R.ptIdealOf_isMaximal
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T13:49:42.242801+00:00
-- url     : https://prove2.me/theorems/035fd9d9-da09-4f69-8de9-9b41af90139f
-- title:
--   R: pt Ideal Of is Maximal
-- statement:
--   The R construction uses the pt Ideal Of is Maximal property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/RegularLocalRings/ConeChartA.lean#L21-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/RegularLocalRings/ConeChartA.lean#L21-L22

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

theorem ReciprocityTheory.AnForm.R.ptIdealOf_isMaximal {σ : Type} (z : σ → ℂ) : (ptIdealOf z).IsMaximal := by sorry
