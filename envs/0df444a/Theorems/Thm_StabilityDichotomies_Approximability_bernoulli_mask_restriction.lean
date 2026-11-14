-- Prove2me | Theorems.Thm_StabilityDichotomies_Approximability_bernoulli_mask_restriction
-- name    : StabilityDichotomies.Approximability.bernoulli_mask_restriction
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T07:21:16.27282+00:00
-- url     : https://prove2.me/theorems/fcb7b385-7f6c-48f5-967b-aaefc22d4cd6
-- title:
--   Bernoulli mask marginal under occurrence reindexing and deletion
-- statement:
--   Let a finite original occurrence set be bijective to an optional index of a finite retained set. For any real p and any real-valued function of the retained Boolean mask, summing against the original Bernoulli product weights gives exactly the Bernoulli-p weighted sum on the retained set. In the range 0 ≤ p ≤ 1 this states that deleting one coordinate and reindexing preserves the independent retention law. This supplies the probability marginal needed for the source deletion coupling.
-- source:
--   Wang and Yoshida, Stability Dichotomies for Boolean Constraint Satisfaction Problems, STOC 2027 submission #535, deletion coupling in proof of Theorem 4.3, p. 17, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/535.pdf

import Mathlib
noncomputable section
open scoped Classical BigOperators

theorem StabilityDichotomies.Approximability.bernoulli_mask_restriction {α β : Type} [Fintype α] [Fintype β]
    (e : α ≃ Option β) (p : ℝ) (g : (β → Bool) → ℝ) :
    (∑ x : α → Bool, (∏ j : α, if x j then p else 1-p) *
      g (fun k => x (e.symm (some k)))) =
    ∑ y : β → Bool, (∏ k : β, if y k then p else 1-p) * g y := by sorry
