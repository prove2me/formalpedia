-- Prove2me | Theorems.Thm_SymmetricPSM1041_ORLowerBound_finite_higman_length_bound
-- name    : SymmetricPSM1041.ORLowerBound.finite_higman_length_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T12:56:10.70924+00:00
-- url     : https://prove2.me/theorems/7303f2b7-34ee-42b4-90c5-64d50ee0bfbb
-- title:
--   Lemma 14 — finite length-indexed Higman bound
-- statement:
--   Let $\Sigma$ be any finite alphabet, including the empty alphabet. There is a positive integer $m$, fixed before the words are chosen, such that every sequence $w_1,\ldots,w_m$ with $|w_i|=i$ has indices
--
--   $$1\le i<j\le m\quad\text{with}\quad w_i\preceq w_j,$$
--
--   where $\preceq$ is the ordinary deletion-subsequence relation. The bound depends only on the alphabet, and no explicit growth rate is asserted. This finite obstruction is one of the two combinatorial prerequisites for agreement.
--
--   Differences from the source:
--   - encoding: words w₁,…,w_m with |w_i|=i → a Fin m-indexed family with length i.val+1 and List.Sublist; reason: zero-based indexing retains all positive lengths and the ordinary deletion relation
-- source:
--   Marshall Ball, Peter Crawford-Kahrl, Vladimir Podolskii, Morgan Prior, STOC 2027 submission #1041 (October 2026), p. 12, Lemma 14; derivation pp. 26–27, Appendix A.1

import Mathlib

namespace SymmetricPSM1041.ORLowerBound

theorem finite_higman_length_bound (Alphabet : Type*) [Fintype Alphabet] :
    ∃ m : ℕ, 1 ≤ m ∧ ∀ w : Fin m → List Alphabet,
      (∀ i, (w i).length = i.val + 1) →
      ∃ i j : Fin m, i < j ∧ (w i).Sublist (w j) := by sorry

end SymmetricPSM1041.ORLowerBound
