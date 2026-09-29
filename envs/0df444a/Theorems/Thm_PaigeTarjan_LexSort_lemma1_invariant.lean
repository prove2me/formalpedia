-- Prove2me | Theorems.Thm_PaigeTarjan_LexSort_lemma1_invariant
-- name    : PaigeTarjan.LexSort.lemma1_invariant
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T17:42:28.956245+00:00
-- url     : https://prove2.me/theorems/207644cd-c23c-4198-b881-e87c251a327a
-- title:
--   Lemma 1 — the finished blocks refine every partition the algorithm reaches
-- statement:
--   Let $U = \{x_1,\dots,x_n\} \subseteq \Sigma^*0$ with $n \ge 1$, and let $P_0 = \{B_\lambda\}, P_1, \dots, P_K$ be any run of the refinement algorithm (each $P_{j+1}$ obtained from $P_j$ by one Refine step). Then for every $j \le K$ and every finished block $B_\beta$ (that is, $\beta = x'_i$ for some $i$):
--
--   1. there is a block $B_\alpha \in P_j$ with $B_\beta \subseteq B_\alpha$, so the partition $F$ of finished blocks is a refinement of $P_j$; and
--   2. there is a block $B_\alpha \in P_j$ such that
--   $$\alpha \text{ is a prefix of } \beta.$$
--
--   This invariant is what makes the algorithm correct: no finished block is ever split, and every finished block stays below some label of the current partition.
--
--   **Formalization Note.** Blocks are compared through their index sets `blk x α`. The hypotheses $n \ge 1$ and $U \subseteq \Sigma^*0$ are the standing assumptions of §2.
-- source:
--   Paige, Tarjan, Three Partition Refinement Algorithms, SIAM J. Comput. 16 (1987), p. 975, Lemma 1

import Mathlib
import Definitions.Def_PaigeTarjan_LexSort_Basic
import Definitions.Def_PaigeTarjan_LexSort_Refine

namespace PaigeTarjan.LexSort

/-- Lemma 1 (p. 975): along every run of the refinement algorithm, the partition `F` of
finished blocks refines the current partition `P` (every finished block is contained in a
block of `P`), and for every finished block `B_β` there is a block `B_α ∈ P` with `α` a
prefix of `β`. -/
theorem lemma1_invariant {k n : ℕ} (x : Fin n → List (Fin (k + 1))) (hn : 0 < n)
    (hx : EndMarked x) (K : ℕ) (Ps : Fin (K + 1) → Finset (List (Fin (k + 1))))
    (hrun : IsRun x K Ps) (j : Fin (K + 1)) :
    (∀ β, IsFinished x β → ∃ α ∈ Ps j, blk x β ⊆ blk x α) ∧
    (∀ β, IsFinished x β → ∃ α ∈ Ps j, α <+: β) := by sorry

end PaigeTarjan.LexSort
