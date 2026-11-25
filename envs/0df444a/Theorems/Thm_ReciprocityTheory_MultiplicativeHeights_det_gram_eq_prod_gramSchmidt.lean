-- Prove2me | Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_det_gram_eq_prod_gramSchmidt
-- name    : ReciprocityTheory.MultiplicativeHeights.det_gram_eq_prod_gramSchmidt
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T11:04:00.82337+00:00
-- url     : https://prove2.me/theorems/51022840-8b31-45a5-b7a4-59e9dd1fb29e
-- title:
--   Multiplicative Heights: det gram eq prod gram Schmidt
-- statement:
--   The Multiplicative Heights construction uses the det gram eq prod gram Schmidt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/DetGramEqProdGramSchmidt.lean#L13-L64
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/DetGramEqProdGramSchmidt.lean#L13-L64

import Mathlib
import Definitions.Def_ReciprocityTheory_SemistableReduction_DetGramEqProdGramSchmidt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.MultiplicativeHeights
open Finset InnerProductSpace

theorem ReciprocityTheory.MultiplicativeHeights.det_gram_eq_prod_gramSchmidt {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (n : ℕ) (v : Fin n → E) :
    (Matrix.gram ℂ v).det = ∏ k, (((‖gramSchmidt ℂ v k‖ ^ 2 : ℝ)) : ℂ) := by sorry
