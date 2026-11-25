-- Prove2me | Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_eval_smul_of_isHomogeneous
-- name    : ReciprocityTheory.MultiplicativeHeights.eval_smul_of_isHomogeneous
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T11:04:16.472006+00:00
-- url     : https://prove2.me/theorems/b5f28e94-88f8-485a-a61e-85927a349999
-- title:
--   Multiplicative Heights: eval smul of is Homogeneous
-- statement:
--   The Multiplicative Heights construction uses the eval smul of is Homogeneous property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/LogNormEvalZeroLeCircleAverage.lean#L39-L49
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/LogNormEvalZeroLeCircleAverage.lean#L39-L49

import Mathlib
import Definitions.Def_ReciprocityTheory_SemistableReduction_LogNormEvalZeroLeCircleAverage
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
open Polynomial

theorem ReciprocityTheory.MultiplicativeHeights.eval_smul_of_isHomogeneous {σ : Type*} {f : MvPolynomial σ ℂ} {a : ℕ}
    (hf : f.IsHomogeneous a) (c : ℂ) (x : σ → ℂ) :
    MvPolynomial.eval (fun i => c * x i) f = c ^ a * MvPolynomial.eval x f := by sorry
