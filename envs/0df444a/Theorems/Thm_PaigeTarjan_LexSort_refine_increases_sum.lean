-- Prove2me | Theorems.Thm_PaigeTarjan_LexSort_refine_increases_sum
-- name    : PaigeTarjan.LexSort.refine_increases_sum
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T17:43:40.665059+00:00
-- url     : https://prove2.me/theorems/01b2be6c-50b4-4c5c-aa67-c2468c2bc70d
-- title:
--   Proof of Theorem 1 — each Refine step increases the total length of the associated prefixes
-- statement:
--   Let $U = \{x_1,\dots,x_n\} \subseteq \Sigma^*0$ with $n \ge 1$, and let $P_0, \dots, P_K$ be any run of the refinement algorithm from $P_0 = \{B_\lambda\}$. Then for every $j < K$,
--   $$\sum_{B_\alpha \in P_j} |\alpha| \;<\; \sum_{B_\alpha \in P_{j+1}} |\alpha|.$$
--
--   Since the sum starts at $0$ and is bounded by $m'$, this gives the explicit termination bound of Theorem 1.
--
--   **Formalization Note.** The hypothesis $n \ge 1$ is needed: for $n = 0$ the block $B_\lambda$ is unfinished and splitting it yields the empty partition, leaving the sum at $0$.
-- source:
--   Paige, Tarjan, Three Partition Refinement Algorithms, SIAM J. Comput. 16 (1987), p. 975, proof of Theorem 1, third sentence

import Mathlib
import Definitions.Def_PaigeTarjan_LexSort_Basic
import Definitions.Def_PaigeTarjan_LexSort_Refine

namespace PaigeTarjan.LexSort

/-- Proof of Theorem 1 (p. 975, third sentence): each Refine step of a run strictly increases
the sum of the lengths of the associated prefixes of the blocks of `P`. -/
theorem refine_increases_sum {k n : ℕ} (x : Fin n → List (Fin (k + 1))) (hn : 0 < n)
    (hx : EndMarked x) (K : ℕ) (Ps : Fin (K + 1) → Finset (List (Fin (k + 1))))
    (hrun : IsRun x K Ps) (j : Fin K) :
    ∑ α ∈ Ps j.castSucc, α.length < ∑ α ∈ Ps j.succ, α.length := by sorry

end PaigeTarjan.LexSort
