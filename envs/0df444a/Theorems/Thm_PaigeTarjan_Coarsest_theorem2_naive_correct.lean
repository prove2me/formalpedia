-- Prove2me | Theorems.Thm_PaigeTarjan_Coarsest_theorem2_naive_correct
-- name    : PaigeTarjan.Coarsest.theorem2_naive_correct
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T17:49:49.126479+00:00
-- url     : https://prove2.me/theorems/06cc28f0-b020-4f4a-8555-205243723964
-- title:
--   Theorem 2, p. 979 — the naïve algorithm is correct and takes at most n − 1 refinement steps
-- statement:
--   Let $E$ be a relation on a nonempty finite set $U$ with $n = |U|$, and let $P$ be a partition of $U$. For every run $Q_0 = P, Q_1, \dots, Q_K$ of the naïve refinement algorithm:
--
--   1. the run has at most $n - 1$ refinement steps, $K \le n - 1$;
--   2. if no refinement step applies to $Q_K$, then $Q_K$ is the coarsest stable refinement of $P$;
--   3. if $Q_K$ is not the coarsest stable refinement of $P$, then a refinement step applies to $Q_K$;
--   4. the coarsest stable refinement of $P$ is unique: if $Q$ and $Q'$ are both coarsest stable refinements of $P$, then $Q = Q'$.
--
--   In short,
--   $$K \le n - 1, \qquad \text{and the algorithm stops exactly at the unique coarsest stable refinement of } P.$$
--
--   Items 1 and 3 together show that the coarsest stable refinement exists and that every maximal run computes it. This is the correctness statement for the naïve algorithm, on which the correctness of the improved algorithm rests.
--
--   **Formalization Note** $K \le n - 1$ is written `K + 1 ≤ n` to avoid natural-number subtraction; $U$ is assumed nonempty, as the paper's count "between one and $n$" blocks presumes.
-- source:
--   Paige, Tarjan, Three Partition Refinement Algorithms, SIAM J. Comput. 16 (1987), p. 979, Theorem 2

import Mathlib
import Definitions.Def_PaigeTarjan_Coarsest_Basic
import Definitions.Def_PaigeTarjan_Coarsest_Algorithms

namespace PaigeTarjan.Coarsest

/-- Theorem 2, p. 979: the naïve refinement algorithm is correct and terminates after at most
`n − 1` refinement steps, having computed the unique coarsest stable partition. For every run of
`K` steps from a partition `P` of a nonempty finite set `U` with `n = |U|`:
(i) `K ≤ n − 1`; (ii) if no refinement step applies to the last state, it is the coarsest stable
refinement of `P`; (iii) if the last state is not the coarsest stable refinement of `P`, a
refinement step applies to it; and (iv) the coarsest stable refinement of `P` is unique. -/
theorem theorem2_naive_correct {U : Type*} [Fintype U] [DecidableEq U] [Nonempty U]
    (E : U → U → Prop) [DecidableRel E] (P : Finset (Finset U)) (hP : IsPartition P)
    (K : ℕ) (Qs : Fin (K + 1) → Finset (Finset U)) (hrun : IsNaiveRun E P K Qs) :
    K + 1 ≤ Fintype.card U ∧
    ((¬ ∃ Q', NaiveStep E (Qs (Fin.last K)) Q') →
      IsCoarsestStableRefinement E P (Qs (Fin.last K))) ∧
    (¬ IsCoarsestStableRefinement E P (Qs (Fin.last K)) →
      ∃ Q', NaiveStep E (Qs (Fin.last K)) Q') ∧
    (∀ Q₁ Q₂ : Finset (Finset U), IsCoarsestStableRefinement E P Q₁ →
      IsCoarsestStableRefinement E P Q₂ → Q₁ = Q₂) := by sorry

end PaigeTarjan.Coarsest
