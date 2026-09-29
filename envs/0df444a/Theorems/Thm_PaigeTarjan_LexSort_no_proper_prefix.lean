-- Prove2me | Theorems.Thm_PaigeTarjan_LexSort_no_proper_prefix
-- name    : PaigeTarjan.LexSort.no_proper_prefix
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T17:41:48.507417+00:00
-- url     : https://prove2.me/theorems/72a28bf2-bb51-488b-a0fe-372a102849f1
-- title:
--   §2 — with end markers, no string of U is a proper prefix of another
-- statement:
--   Let $U = \{x_1,\dots,x_n\}$ be a multiset of strings in $\Sigma^*0$, that is, each $x_i$ is a string over $\Sigma = \{1,\dots,k\}$ followed by a single end marker $0$. Then for all $i, j$:
--   $$x_i \text{ is a prefix of } x_j \;\Longrightarrow\; x_i = x_j.$$
--   Equivalently, no string of $U$ is a proper prefix of another string of $U$.
--
--   This is the structural fact behind the uniqueness of distinguishing prefixes and behind Lemma 1: an unfinished label is always a proper prefix of each finished label below it.
--
--   **Formalization Note.** $U$ is a family `x : Fin n → List (Fin (k + 1))` with the hypothesis `EndMarked x`.
-- source:
--   Paige, Tarjan, Three Partition Refinement Algorithms, SIAM J. Comput. 16 (1987), p. 974, §2, paragraph after the definition of the distinguishing prefix, first sentence

import Mathlib
import Definitions.Def_PaigeTarjan_LexSort_Basic

namespace PaigeTarjan.LexSort

/-- §2, p. 974: because the end marker `0` occurs only in the last position of a string, no
string in `U` is a proper prefix of another string in `U`. -/
theorem no_proper_prefix {k n : ℕ} (x : Fin n → List (Fin (k + 1))) (hx : EndMarked x)
    (i j : Fin n) (hij : x i <+: x j) : x i = x j := by sorry

end PaigeTarjan.LexSort
