-- Prove2me | Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_approxB_sum_neg
-- name    : ReciprocityTheory.MultiplicativeHeights.approxB_sum_neg
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T14:28:51.620581+00:00
-- url     : https://prove2.me/theorems/c9eefa7f-b107-4e9d-bf51-e8d74871628e
-- title:
--   Multiplicative Heights: approx B sum neg
-- statement:
--   The Multiplicative Heights construction uses the approx B sum neg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/ApproxBasisA.lean#L99-L104
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/ApproxBasisA.lean#L99-L104

import Definitions.Def_ReciprocityTheory_SemistableReduction_TorsionNonvanishStatement
import Definitions.Def_ReciprocityTheory_SemistableReduction_ApproxBasisA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.MultiplicativeHeights
open Matrix NumberField ComplexConjugate
open scoped ComplexOrder

theorem ReciprocityTheory.MultiplicativeHeights.approxB_sum_neg {M : Type*} [AddCommMonoid M] {r p : ℕ} (f : Fin r → M)
    (hf : ∀ j : Fin r, (j : ℕ) < p → f j = 0) :
    ∑ j, f j = ∑ k : {j : Fin r // ¬ (j : ℕ) < p}, f k := by sorry
