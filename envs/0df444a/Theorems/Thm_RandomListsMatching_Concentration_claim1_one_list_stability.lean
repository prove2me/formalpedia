-- Prove2me | Theorems.Thm_RandomListsMatching_Concentration_claim1_one_list_stability
-- name    : RandomListsMatching.Concentration.claim1_one_list_stability
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T20:08:47.736852+00:00
-- url     : https://prove2.me/theorems/b638ea66-62e4-401c-b14e-2c7cc3371166
-- title:
--   Claim 1, p. 5 — changing one list changes the cardinality of the resulting matching by at most one
-- statement:
--   Let $A$ be a set of advertisers and let $(l_1, \dots, l_n)$ and $(l'_1, \dots, l'_n)$ be two sequences of lists of advertisers that differ in at most one position $t$, that is, $l_j = l'_j$ for all $j \ne t$. Run the list-greedy rule of the Random Lists Algorithms on each: every request is assigned to the first not-yet-matched advertiser of its list, or dropped if there is none. Then the cardinalities of the two resulting matchings differ by at most one:
--   $$
--   \bigl|\mathrm{alg}(l_1, \dots, l_n) - \mathrm{alg}(l'_1, \dots, l'_n)\bigr| \le 1 .
--   $$
--
--   This is the bounded-difference property that makes McDiarmid's inequality applicable to ALG as a function of the i.i.d. lists, and so yields Lemma 1.
--
--   **Formalization Note** The statement concerns arbitrary list sequences; no graph and no interestedness of the lists is needed. The difference is taken in $\mathbb Z$.
-- source:
--   Jaillet & Lu, Online Stochastic Matching: New Algorithms with Better Bounds, accepted manuscript (rev. June 2013), p. 5, Claim 1

import Mathlib
import Definitions.Def_RandomListsMatching_Concentration_Setting

namespace RandomListsMatching.Concentration

/-- **Claim 1** (Jaillet & Lu, accepted manuscript (rev. June 2013), §2, p. 5). If two
realizations of the lists differ only in the list of request `t`, the cardinalities of their
resulting matchings differ by at most one. -/
theorem claim1_one_list_stability {A : Type} [DecidableEq A] {n : ℕ} (ls ls' : Fin n → List A)
    (t : Fin n) (hdiff : ∀ j, j ≠ t → ls j = ls' j) :
    |(algValue ls : ℤ) - (algValue ls' : ℤ)| ≤ 1 := by sorry

end RandomListsMatching.Concentration
