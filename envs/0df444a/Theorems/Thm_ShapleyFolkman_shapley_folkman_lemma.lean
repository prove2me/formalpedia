-- Prove2me | Theorems.Thm_ShapleyFolkman_shapley_folkman_lemma
-- name    : ShapleyFolkman.shapley_folkman_lemma
-- status  : Proved
-- author  : @Nickrobbins95
-- created : 2026-10-05T01:36:21.931319+00:00
-- url     : https://prove2.me/theorems/c0ad8fea-9ca6-4571-a8b5-2733d8b26f15
-- title:
--   Shapley–Folkman lemma
-- statement:
--   **Shapley–Folkman lemma.** Let $N \ge 0$ and $m \ge 0$ be integers and let $S_1, \dots, S_m$ be arbitrary (not necessarily convex, closed or bounded) subsets of the Euclidean space $\mathbb{R}^N$. Their Minkowski sum is
--
--   $$
--   S_1 + \cdots + S_m = \{\, s_1 + \cdots + s_m : s_i \in S_i \text{ for } i = 1, \dots, m \,\},
--   $$
--
--   and $\operatorname{conv} A$ denotes the convex hull of a set $A \subseteq \mathbb{R}^N$. If
--
--   $$
--   x \in \operatorname{conv}(S_1 + \cdots + S_m),
--   $$
--
--   then there are points $x_i \in \operatorname{conv} S_i$ $(i = 1, \dots, m)$ such that
--
--   $$
--   x = \sum_{i=1}^{m} x_i \qquad\text{and}\qquad \#\{\, i : x_i \notin S_i \,\} \le N .
--   $$
--
--   In words: every point of the convex hull of a Minkowski sum can be written as a sum of points taken from the convex hulls of the summands, where all but at most $N$ of these points already lie in the original sets $S_i$.
--
--   Because $\operatorname{conv}(S_1 + \cdots + S_m) = \operatorname{conv} S_1 + \cdots + \operatorname{conv} S_m$, the lemma says that a Minkowski sum of many sets is close to convex: the defect is confined to at most $N$ summands, however large $m$ is. It is the key step in Starr's construction of approximate (quasi-)equilibria for markets with non-convex preferences, and it underlies the small duality gap of separable non-convex optimization problems with many terms.
--
--   **Formalization Note** $\mathbb{R}^N$ is `EuclideanSpace ℝ (Fin N)` and the family is indexed by `Fin m`. The Minkowski sum is the pointwise sum of sets `∑ i, S i` (scope `Pointwise`), and the number of exceptional indices is `Set.ncard {i | y i ∉ S i}`. No nonemptiness hypothesis is stated: if some $S_i$ is empty, the Minkowski sum is empty and the hypothesis on $x$ cannot hold. The degenerate cases $m = 0$ and $N = 0$ are included.
-- source:
--   R. M. Starr, Quasi-equilibria in markets with non-convex preferences, Econometrica 37(1) (1969), 25–38, Appendix: the Shapley–Folkman theorem (due to L. S. Shapley and J. H. Folkman); L. Zhou, A simple proof of the Shapley–Folkman theorem, Economic Theory 3(2) (1993), 371–372, the Shapley–Folkman theorem stated on p. 371; see also https://en.wikipedia.org/wiki/Shapley%E2%80%93Folkman_lemma

import Mathlib
open scoped Pointwise

namespace ShapleyFolkman

theorem shapley_folkman_lemma (N m : ℕ) (S : Fin m → Set (EuclideanSpace ℝ (Fin N)))
    (x : EuclideanSpace ℝ (Fin N)) (hx : x ∈ convexHull ℝ (∑ i, S i)) :
    ∃ y : Fin m → EuclideanSpace ℝ (Fin N),
      (∀ i, y i ∈ convexHull ℝ (S i)) ∧ ∑ i, y i = x ∧
        {i | y i ∉ S i}.ncard ≤ N := by
  sorry

end ShapleyFolkman
