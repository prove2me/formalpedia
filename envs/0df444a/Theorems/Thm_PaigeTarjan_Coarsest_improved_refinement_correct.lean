-- Prove2me | Theorems.Thm_PaigeTarjan_Coarsest_improved_refinement_correct
-- name    : PaigeTarjan.Coarsest.improved_refinement_correct
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T17:51:31.869602+00:00
-- url     : https://prove2.me/theorems/4c62bdb7-22a1-40e0-979d-fe503f0a121c
-- title:
--   The improved (smaller-half) refinement algorithm computes the coarsest stable refinement; each element lies in at most log₂ n + 1 refining blocks
-- statement:
--   Let $E$ be a relation on a nonempty finite set $U$ with $n = |U|$, satisfying the standing assumption $|E(\{x\})| \ge 1$ for every $x \in U$ (every element has at least one $E$-successor), and let $P$ be a partition of $U$. Consider any run of the improved refinement algorithm,
--   $$(Q_0, X_0) = (P, \{U\}),\ (Q_1, X_1),\ \dots,\ (Q_K, X_K),$$
--   where step $j$ chooses a block $S_j \in X_j$ that is not a block of $Q_j$ and a block $B_j \in Q_j$ with $B_j \subseteq S_j$ and $|B_j| \le |S_j|/2$, replaces $S_j$ within $X_j$ by $B_j$ and $S_j - B_j$, and sets $Q_{j+1} = \mathrm{split}(S_j - B_j, \mathrm{split}(B_j, Q_j))$. Then:
--
--   1. (invariant) for every $j$, $Q_j$ and $X_j$ are partitions of $U$, $Q_j$ is a refinement of $X_j$, and $Q_j$ is stable with respect to every block of $X_j$;
--   2. (correctness) if $Q_K = X_K$, then $Q_K$ is the coarsest stable refinement of $P$;
--   3. (progress) if $Q_K \neq X_K$, a further refinement step applies to $(Q_K, X_K)$;
--   4. (termination) $K \le n - 1$;
--   5. (smaller half) every element $x \in U$ lies in the refining block of at most $\log_2 n + 1$ steps:
--   $$\#\{\, j < K \mid x \in B_j \,\} \le \log_2 n + 1.$$
--
--   Items 1–4 say that the algorithm, whatever choices it makes, stops after at most $n-1$ steps at the coarsest stable refinement of $P$. Item 5 is the counting fact behind the $O(m \log n)$ running time of the Paige–Tarjan algorithm, where $m = |E|$.
--
--   **Formalization Note** The standing assumption of p. 979 is the hypothesis `∀ x, ∃ y, E x y`; without it the initial state $(P, \{U\})$ need not satisfy the invariant. $U$ is assumed nonempty so that $\{U\}$ is a partition. Item 4 is not printed for the improved algorithm; it is derived as in the proof of Theorem 2 (each step adds one block to $X$) and is written `K + 1 ≤ n`. Item 5 counts step indices, which is at least as strong as counting distinct refining sets; $\log_2$ is `Real.logb 2` applied to $n$ cast to $\mathbb{R}$. Running times are not formalized.
-- source:
--   Paige, Tarjan, Three Partition Refinement Algorithms, SIAM J. Comput. 16 (1987), p. 979, last two paragraphs (standing assumption, improved algorithm) and p. 980, first paragraph (correctness) and paragraph after Lemma 3 (log₂ n + 1 bound)

import Mathlib
import Definitions.Def_PaigeTarjan_Coarsest_Basic
import Definitions.Def_PaigeTarjan_Coarsest_Algorithms

namespace PaigeTarjan.Coarsest

/-- The improved ("process the smaller half") refinement algorithm, pp. 979–980, under the
standing assumption `|E({x})| ≥ 1` for all `x ∈ U` (p. 979). For every run of `K` steps from
`(Q, X) = (P, {U})`, where `P` is a partition of the nonempty finite set `U` and `n = |U|`:
(1) at every stage `Q` and `X` are partitions of `U`, `Q` is a refinement of `X`, and `Q` is
stable with respect to every block of `X`;
(2) if the last state has `Q = X`, then `Q` is the coarsest stable refinement of `P`;
(3) if the last state has `Q ≠ X`, a further refinement step applies;
(4) `K ≤ n − 1` (derived as in the proof of Theorem 2; not printed for this algorithm);
(5) every element `x ∈ U` lies in the refining block `B` of at most `log₂ n + 1` steps. -/
theorem improved_refinement_correct {U : Type*} [Fintype U] [DecidableEq U] [Nonempty U]
    (E : U → U → Prop) [DecidableRel E] (hE : ∀ x : U, ∃ y : U, E x y)
    (P : Finset (Finset U)) (hP : IsPartition P)
    (K : ℕ) (Qs Xs : Fin (K + 1) → Finset (Finset U)) (Ss Bs : Fin K → Finset U)
    (hrun : IsImprovedRun E P K Qs Xs Ss Bs) :
    (∀ j : Fin (K + 1), IsPartition (Qs j) ∧ IsPartition (Xs j) ∧
      Refines (Qs j) (Xs j) ∧ ∀ S ∈ Xs j, StableWrt E (Qs j) S) ∧
    (Qs (Fin.last K) = Xs (Fin.last K) →
      IsCoarsestStableRefinement E P (Qs (Fin.last K))) ∧
    (Qs (Fin.last K) ≠ Xs (Fin.last K) →
      ∃ (S B : Finset U) (Q' X' : Finset (Finset U)),
        ImprovedStep E (Qs (Fin.last K)) (Xs (Fin.last K)) S B Q' X') ∧
    K + 1 ≤ Fintype.card U ∧
    (∀ x : U, ((Finset.univ.filter (fun j : Fin K => x ∈ Bs j)).card : ℝ) ≤
      Real.logb 2 (Fintype.card U) + 1) := by sorry

end PaigeTarjan.Coarsest
