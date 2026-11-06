-- Prove2me | Theorems.Thm_TreeMultiflow_lemma_A_1
-- name    : TreeMultiflow.lemma_A_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-05T23:58:13.421268+00:00
-- url     : https://prove2.me/theorems/78a6029c-5e74-4baf-84a9-c4d6af4a98c5
-- title:
--   Lemma A.1 (packing lemma): items of sizes in $\{1,\dots,6\}$ and total size at most $4u+2$ fit into $u$ bins of size six
-- statement:
--   Let $u\ge 1$ be an integer. Any collection of indivisible items with positive integer sizes at most six and total size at most $4u+2$ can be packed into at most $u$ bins, each having total size at most six, without splitting any item. In symbols: if $s_i\in\{1,\dots,6\}$ for every item $i$ and $\sum_i s_i\le 4u+2$, there is an assignment $\beta$ of the items to bins $1,\dots,u$ with
--   $$
--   \sum_{i:\ \beta(i)=k} s_i\le 6\qquad\text{for every bin } k.
--   $$
--
--   In the proofs of Theorems 3.1 and 5.2 the items are the crossing blocks of a contracted star, and the lemma provides the new bins at the contracted leaf.
--
--   Differences from the source:
--   - encoding: packed into at most u bins without splitting any item → an assignment β : I → Fin u (each item to one bin; empty bins allowed); reason: a packing into at most u bins is the same as an assignment into u bins
--   - encoding: any collection of items → a finite type I of items; reason: sizes are positive and the total size is finite, so there are finitely many items; same instances
-- source:
--   Harb, Improved Integrality Gap for Multicommodity Flow on Trees, arXiv:2609.07949, Lemma A.1, p.11

import Mathlib

namespace TreeMultiflow

/-- **Lemma A.1 (packing lemma).**
Harb, *Improved Integrality Gap for Multicommodity Flow on Trees*, arXiv:2609.07949, Lemma A.1,
p.11: "Let u ≥ 1 be an integer. Any collection of indivisible items with positive integer sizes at
most six and total size at most 4u + 2 can be packed into at most u bins, each having total size at
most six, without splitting any item."

For a finite collection of items `I` with sizes `s i ∈ {1, …, 6}` and `Σ s ≤ 4u + 2`, there is an
assignment `β` of every item to one of `u` bins with total size at most six in every bin.

**Formalization Note.** An item is not split because `β` sends each item to a single bin. "At
most u bins" is an assignment into `Fin u`; bins that receive no item are allowed. -/
theorem lemma_A_1 (u : ℕ) (hu : 1 ≤ u) {I : Type*} [Fintype I] (s : I → ℕ)
    (hs : ∀ i, 1 ≤ s i ∧ s i ≤ 6) (htot : ∑ i, s i ≤ 4 * u + 2) :
    ∃ β : I → Fin u, ∀ k : Fin u, ∑ i ∈ Finset.univ.filter (fun i => β i = k), s i ≤ 6 := by sorry

end TreeMultiflow
