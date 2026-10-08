-- Prove2me | Theorems.Thm_TreewidthApprox_Partition_lemma_6_3
-- name    : TreewidthApprox.Partition.lemma_6_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T07:42:58.745603+00:00
-- url     : https://prove2.me/theorems/a455a575-c508-4f0d-ade9-39b3cd8c3967
-- title:
--   Lemma 6.3 — partition nonnegative integers into three half-bounded classes
-- statement:
--   Let $a_1,\ldots,a_p$ be nonnegative integers with total $q$, and suppose each $a_i\le q/2$. Then their indices can be partitioned into three classes $I_1,I_2,I_3$ such that
--
--   $$
--   \sum_{i\in I_j}a_i\le q/2\qquad(j=1,2,3).
--   $$
--
--   This observation groups the weights of graph components into the three parts required by Lemma 2.9.
--
--   **Formalization Note** The classes may be empty, including when $p<3$. Partitioning indices distinguishes equal-valued integers. The half bounds are expressed as $2a_i\le q$ and $2\sum_{i\in I_j}a_i\le q$ over natural numbers.
-- source:
--   Bodlaender, Drange, Dregi, Fomin, Lokshtanov and Pilipczuk, A c^k n 5-approximation algorithm for treewidth, SIAM J. Comput. 45(2) (2016), p. 363, Lemma 6.3, https://doi.org/10.1137/130947374

import Mathlib

namespace TreewidthApprox.Partition

/-- Lemma 6.3, p. 363: items of size at most half of their total can be
partitioned into three classes, each of size at most half of the total. -/
theorem lemma_6_3 (p : ℕ) (a : Fin p → ℕ) (q : ℕ)
    (hq : ∑ i, a i = q) (ha : ∀ i, 2 * a i ≤ q) :
    ∃ c : Fin p → Fin 3,
      ∀ j : Fin 3, 2 * ∑ i ∈ Finset.univ.filter (fun i => c i = j), a i ≤ q := by sorry

end TreewidthApprox.Partition
