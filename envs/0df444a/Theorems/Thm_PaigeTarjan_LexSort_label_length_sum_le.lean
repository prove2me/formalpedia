-- Prove2me | Theorems.Thm_PaigeTarjan_LexSort_label_length_sum_le
-- name    : PaigeTarjan.LexSort.label_length_sum_le
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T17:43:04.95679+00:00
-- url     : https://prove2.me/theorems/b46801e1-0d36-4d41-ad10-a10362bf6ac8
-- title:
--   Proof of Theorem 1 — the associated prefixes of P have total length at most m′
-- statement:
--   Let $U = \{x_1,\dots,x_n\} \subseteq \Sigma^*0$ with $n \ge 1$, and let $P_0, \dots, P_K$ be any run of the refinement algorithm from $P_0 = \{B_\lambda\}$. Then for every $j \le K$,
--   $$\sum_{B_\alpha \in P_j} |\alpha| \;\le\; m' = \sum_{i=1}^n |x'_i|.$$
--
--   Together with the fact that every Refine step increases the left-hand side, this bounds the number of refinement steps by $m'$.
--
--   **Formalization Note.** The sum ranges over the set of labels of $P_j$.
-- source:
--   Paige, Tarjan, Three Partition Refinement Algorithms, SIAM J. Comput. 16 (1987), p. 975, proof of Theorem 1, second sentence

import Mathlib
import Definitions.Def_PaigeTarjan_LexSort_Basic
import Definitions.Def_PaigeTarjan_LexSort_Refine

namespace PaigeTarjan.LexSort

/-- Proof of Theorem 1 (p. 975, second sentence): in every state reached by the refinement
algorithm, the sum of the lengths of the associated prefixes of the blocks of `P` is at most
`m′`. -/
theorem label_length_sum_le {k n : ℕ} (x : Fin n → List (Fin (k + 1))) (hn : 0 < n)
    (hx : EndMarked x) (K : ℕ) (Ps : Fin (K + 1) → Finset (List (Fin (k + 1))))
    (hrun : IsRun x K Ps) (j : Fin (K + 1)) :
    ∑ α ∈ Ps j, α.length ≤ mPrime x := by sorry

end PaigeTarjan.LexSort
