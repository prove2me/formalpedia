-- Prove2me | Theorems.Thm_TreewidthApprox_Partition_merge_step
-- name    : TreewidthApprox.Partition.merge_step
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T07:42:56.805766+00:00
-- url     : https://prove2.me/theorems/c3f6efff-d1ed-4faf-8201-d4c9c4f61e14
-- title:
--   Proof of Lemma 6.3 — the two smallest set sums total at most half
-- statement:
--   Let $m\ge4$ sets have nonnegative integer sums $b_1,\ldots,b_m$. Select two distinct sets $i,j$ whose sums are each no greater than every other set's sum. Then
--
--   $$
--   2(b_i+b_j)\le\sum_{\ell=1}^{m}b_\ell.
--   $$
--
--   This is the bound on a single merge in the paper's three-partition observation.
--
--   **Formalization Note** The finite family may contain zero sums. The two selected indices are distinct; their order is irrelevant.
-- source:
--   Bodlaender, Drange, Dregi, Fomin, Lokshtanov and Pilipczuk, A c^k n 5-approximation algorithm for treewidth, SIAM J. Comput. 45(2) (2016), p. 364, proof of Lemma 6.3, merge paragraph, https://doi.org/10.1137/130947374

import Mathlib

namespace TreewidthApprox.Partition

/-- Proof of Lemma 6.3, p. 364: among at least four set sums, the two smallest
together account for at most half of the total. -/
theorem merge_step (m : ℕ) (hm : 4 ≤ m) (b : Fin m → ℕ) (i j : Fin m) (hij : i ≠ j)
    (hmin : ∀ l, l ≠ i → l ≠ j → b i ≤ b l ∧ b j ≤ b l) :
    2 * (b i + b j) ≤ ∑ l, b l := by sorry

end TreewidthApprox.Partition
