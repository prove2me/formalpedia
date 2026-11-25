-- Prove2me | Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_bwp_eval_aeval_X
-- name    : ReciprocityTheory.MultiplicativeHeights.bwp_eval_aeval_X
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T11:03:58.78982+00:00
-- url     : https://prove2.me/theorems/22bbb4f2-6262-45e1-898e-4be0adb3ecff
-- title:
--   Multiplicative Heights: bwp eval aeval X
-- statement:
--   The Multiplicative Heights construction uses the bwp eval aeval X property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/BWPolyA.lean#L32-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/BWPolyA.lean#L32-L36

import Mathlib
import Definitions.Def_ReciprocityTheory_SemistableReduction_BWPolyA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.MultiplicativeHeights
open Polynomial

theorem ReciprocityTheory.MultiplicativeHeights.bwp_eval_aeval_X {σ : Type*} (L : ℂ[X]) (i : σ) (y : σ → ℂ) :
    MvPolynomial.eval y (Polynomial.aeval (MvPolynomial.X i : MvPolynomial σ ℂ) L) = L.eval (y i) := by sorry
