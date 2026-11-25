-- Prove2me | Theorems.Thm_PI_WickFormula_add_pow_smul
-- name    : PI.WickFormula.add_pow_smul
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T05:47:05.015859+00:00
-- url     : https://prove2.me/theorems/69acee4f-c972-41d3-8410-f462f1399fa4
-- title:
--   Wick Formula: add pow smul
-- statement:
--   The Wick Formula construction uses the add pow smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/TaylorDiscriminants/DiscriminantEstimates/DiscriminantLemmas/WickFormula/LprodAddSmul.lean#L14-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/TaylorDiscriminants/DiscriminantEstimates/DiscriminantLemmas/WickFormula/LprodAddSmul.lean#L14-L20

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_DiscriminantEstimates_DiscriminantLemmas_WickFormula_OrdEvalEqSumOf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_DiscriminantEstimates_DiscriminantLemmas_WickFormula_LprodAddSmul
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
open PI PI.WickFormula
variable {AA : Type} [Ring AA]

theorem PI.WickFormula.add_pow_smul {M : Type} [AddCommGroup M] [Module AA M] (x y : AA) (w : M)
    (hxy : Commute y x) (hw : y • w = 0) (n : ℕ) : (x + y) ^ n • w = x ^ n • w := by sorry
