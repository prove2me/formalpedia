-- Prove2me | Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_eval_aeval_alt
-- name    : ReciprocityTheory.MultiplicativeHeights.eval_aeval_alt
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T11:04:09.46189+00:00
-- url     : https://prove2.me/theorems/778f0d14-6023-40e3-a907-977fab3d09e7
-- title:
--   Multiplicative Heights: eval aeval alt
-- statement:
--   The Multiplicative Heights construction uses the eval aeval alt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/RestBlockSubstIsMultiHomogeneous.lean#L25-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/RestBlockSubstIsMultiHomogeneous.lean#L25-L30

import Definitions.Def_ReciprocityTheory_SemistableReduction_AevalIsWeightedHomogeneous
import Definitions.Def_ReciprocityTheory_SemistableReduction_RestBlockSubstIsMultiHomogeneous
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
open MeasureTheory MvPolynomial

theorem ReciprocityTheory.MultiplicativeHeights.eval_aeval_alt {σ τ : Type*} (v : σ → MvPolynomial τ ℂ) (x : τ → ℂ)
    (g : MvPolynomial σ ℂ) : eval x (aeval v g) = eval (fun i => eval x (v i)) g := by sorry
