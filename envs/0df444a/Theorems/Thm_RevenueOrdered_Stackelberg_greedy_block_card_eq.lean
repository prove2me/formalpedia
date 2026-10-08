-- Prove2me | Theorems.Thm_RevenueOrdered_Stackelberg_greedy_block_card_eq
-- name    : RevenueOrdered.Stackelberg.greedy_block_card_eq
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T04:06:08.599389+00:00
-- url     : https://prove2.me/theorems/fd9d50ac-3c87-4518-b494-cdf5aaa8aa6d
-- title:
--   (14) — orderings that agree on a block partition make greedy pick the same number of elements in each block
-- statement:
--   Let $M=(E,\mathcal X)$ be a matroid with finite ground set $E$, partitioned into blocks $E_1,E_2,\dots$. Let $L$ and $L'$ be two linear orderings of $E$ that agree on this partition: for $i<j$, every $e\in E_i$ precedes every $f\in E_j$, both in $L$ and in $L'$. Then for every block index $i$,
--   $$
--   |\mathrm{greedy}_M(E,L)\cap E_i|=|\mathrm{greedy}_M(E,L')\cap E_i|.
--   $$
--
--   Inside a block the two orderings may differ arbitrarily; the property says that how ties are broken inside blocks does not affect how many elements of each block greedy selects. The paper derives Lemma 4.15 from it.
--
--   **Formalization Note** The blocks are the fibres $E_i=\{e\in E:\mathrm{blk}(e)=i\}$ of a function $\mathrm{blk}:E\to\mathbb N$ (empty blocks are allowed), and "$e$ precedes $f$ in $L$" is `[e, f].Sublist L`. The paper states the agreement only for consecutive blocks $E_i,E_{i+1}$ and indexes the blocks to $k$ after naming $\ell$ of them; agreement for all $i<j$ is the intended condition (consecutive agreement does not order two blocks separated by an empty block).
-- source:
--   Berbeglia & Joret, Assortment Optimisation Under a General Discrete Choice Model: A Tight Analysis of Revenue-Ordered Assortments, arXiv:1606.01371v3, p. 31, proof of Lemma 4.15, (14)

import Mathlib
import Definitions.Def_RevenueOrdered_Stackelberg_Greedy

open Classical

namespace RevenueOrdered.Stackelberg

/-- Property (14) (Berbeglia–Joret, arXiv:1606.01371v3, proof of Lemma 4.15, p. 31). Let the
finite ground set `E` of a matroid `M` be partitioned into blocks `E_i = {e ∈ E : blk e = i}`,
and let `L`, `L'` be two linear orderings of `E` that agree on the block partition: every element
of a lower-indexed block precedes every element of a higher-indexed block, in both orderings.
Then the greedy algorithm picks the same number of elements in each block under `L` and `L'`. -/
theorem greedy_block_card_eq {α : Type*} (M : Matroid α) (E : Finset α)
    (hE : (E : Set α) = M.E) (L L' : List α) (hL : IsLinearOrderOf L E)
    (hL' : IsLinearOrderOf L' E) (blk : α → ℕ)
    (hagree : ∀ e ∈ E, ∀ f ∈ E, blk e < blk f → [e, f].Sublist L ∧ [e, f].Sublist L') :
    ∀ i : ℕ, ((greedyM M L E).filter (fun e => blk e = i)).card =
      ((greedyM M L' E).filter (fun e => blk e = i)).card := by sorry

end RevenueOrdered.Stackelberg
