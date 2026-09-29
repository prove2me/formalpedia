-- Prove2me | Theorems.Thm_PaigeTarjan_LexSort_theorem1_terminates_and_correct
-- name    : PaigeTarjan.LexSort.theorem1_terminates_and_correct
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T17:44:42.931306+00:00
-- url     : https://prove2.me/theorems/6e5150a5-9b04-4727-bb0e-899697a6b9bf
-- title:
--   Theorem 1 — the refinement algorithm terminates within m′ steps and is correct
-- statement:
--   Let $\Sigma = \{1,\dots,k\}$, and let $U = \{x_1,\dots,x_n\}$, $n \ge 1$, be a multiset of strings in $\Sigma^*0$ (each a string over $\Sigma$ followed by a single end marker $0$). Let $x'_i$ be the distinguishing prefix of $x_i$ in $U$ and $m' = \sum_{i=1}^n |x'_i|$.
--
--   Consider any run $P_0 = \{B_\lambda\}, P_1, \dots, P_K$ of the refinement algorithm, in which each $P_{j+1} = \mathrm{split}(B_\alpha, P_j)$ for some unfinished block $B_\alpha \in P_j$. Then:
--
--   1. (termination) the number of refinement steps satisfies
--   $$K \le m';$$
--   2. (correctness) if no block of $P_K$ is unfinished, so that Refine no longer applies, then $P_K$ is the finished partition: its labels are exactly the distinguishing prefixes $\{x'_1, \dots, x'_n\}$.
--
--   Hence the algorithm, run until no unfinished block remains, stops after at most $m'$ steps with the set of all distinguishing prefixes. This is the first of the two steps of the paper's lexicographic sorting algorithm.
--
--   **Formalization Note.** The paper states "The algorithm terminates and is correct"; the bound $K \le m'$ is the explicit form proved on p. 975 in the last sentence of the proof. The running time $O(m' + k)$ is a RAM-model bound and is not formalized. The hypothesis $n \ge 1$ (the paper's $x_1, \dots, x_n$) is needed: with $n = 0$ one Refine step is possible while $m' = 0$.
-- source:
--   Paige, Tarjan, Three Partition Refinement Algorithms, SIAM J. Comput. 16 (1987), p. 975, Theorem 1 and its proof (bound: last sentence of the proof)

import Mathlib
import Definitions.Def_PaigeTarjan_LexSort_Basic
import Definitions.Def_PaigeTarjan_LexSort_Refine

namespace PaigeTarjan.LexSort

/-- Theorem 1 (p. 975), with the explicit bound of its proof: every run of the refinement
algorithm has at most `m′ = ∑ᵢ |x′ᵢ|` Refine steps, and a state reached in which no block is
unfinished (so no Refine step applies) is the finished partition, whose labels are exactly the
distinguishing prefixes. -/
theorem theorem1_terminates_and_correct {k n : ℕ} (x : Fin n → List (Fin (k + 1)))
    (hn : 0 < n) (hx : EndMarked x) (K : ℕ)
    (Ps : Fin (K + 1) → Finset (List (Fin (k + 1)))) (hrun : IsRun x K Ps) :
    K ≤ mPrime x ∧
    ((∀ α ∈ Ps (Fin.last K), IsFinished x α) → Ps (Fin.last K) = finishedLabels x) := by sorry

end PaigeTarjan.LexSort
